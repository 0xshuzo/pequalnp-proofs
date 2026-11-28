import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_52262.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_52262
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffeefffffffefffffefe,0xffeeffeeeeccaa00ffff,0xffffffffffffffffffff,0xffffffeefffffffeffff,0xfefeffeeffeeeeccaa00]))
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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

private def sixWordsP0 : Array Nat := #[53957959491618,36322559942760,114668244967458,158890167832851,88245472006419,176482353815586,158890167767058,36322555732008,44122736101899,142423263675147,61684723097634,89142331588674,176508128223336,150089779841547,211726858477680,123386626441995,211666725912642,176508124012584,143557135500051,176508124136203,54357915599169,72645111464016,88245471940626,114767431928331,142663785382209,81411272949825,73748934836304,211662430879809,176478058782753,114663949934625,150089779709961,142423267762280,159511075782786,36456219935499,142526344331553,80712235483425,38530202476584,46226900852769,211692496225035,211726856372304,123567819919635,54357915599426,10037357445160,150222925725736,81811747111458,72645113569392,12412627452225,141875671998504,142423263551528,142116193861824,142663785382466,246738892489483,123567819853842,89142332115018,142457623806482,176094196663051,151780017143937,81475698442320,61783910977561,141875672023176,176478059835441,114728375485203,211726856422163,114767431796745]
private def sixWordsP1 : Array Nat := #[142457625927792,123356561096769,220350212243616,73748936941680,143763297010242,141978752811168,71812927980050,150222929938536,176542484333331,142526348544104,88245471936530,150089780762649,123360856129602,158407269187714,107616319570305,143557135434258,142457623822416,12206465892432,158619584827410,211666725838881,12687509553537,220281491751699,12206467997808,36732171584267,176370148311819,141875676209256,107100915761931,81811747111201,159511075766338,44122735968265,246738892390536,53983729688616,176478058856514,89620935217170,143082576183456,143625855959586,72054519497483,141884299698280,12275186401569,55457427227202,143018169491568,142423263674891,10037361655912,107100915630345,158890167762962,44122737023001,114767431926283,61783910056459,114492554021387,37555732484377,10037361657960,142423264596249,81124558635393,193755370619659,142526345384241,46226901905457,150222925725985,142423263543561,53983730741304,36870147408651,143557135450192,176478058790977,211662430937122,143522779390056]
private def sixWordsP2 : Array Nat := #[143522775179304,36971623743873,143013855641680,150222926778424,211450904773395,71506927820840,211662430945346,141918657863792,53957959499842,36972697485697,176094196531465,107135275893266,72293971657601,141978786365600,176542484283472,211666726438986,44122736099851,144083322953832,159536850165864,176068426367106,144117679013968,143013855658128,158890168293402,61783910058507,20074714890320,152050604212416,176094197584153,158673544413762,144083318767752,72912439673619,246708827160705,61783910979609,176508124004617,72156532703617,123386626310409,109472274989136,38564562747472,159156459798608,150222929936488,176482353758273,114663950024834,36766531797072,211692496101416,53957959516290,89142331605122,72293971657346,36456219836552,108234787521042,143625855959329,36971623744385,10449680597128,36322555723816,53983729680424,176508124004392,108200427258121,246738892357897,97076058980627,44019254100001,211390774317331,73748934852752,12245004189736,211666725966099,193995892326978,150089779839499]
private def sixWordsP3 : Array Nat := #[44122737020953,150089780760601,12245008400488,27698535612520,107238891462696,176237541072936,142397493362754,115209419096706,211390774280322,97076058918930,97076058914834,123567819849746,107100915761675,220350212210977,150089779710473,71812928506394,176508125065272,246773252686611,167233544355969,97076058984723,211692497146137,144117679030416,159156459799106,142457624348760,38530206687336,211386479247489,141875673051192,149705516384545,88038508216386,193725305290881,97076059445274,96864800161857]
private def sixWords : Array (Array Nat) := #[sixWordsP0,sixWordsP1,sixWordsP2,sixWordsP3]
private def sixMenuStartsP0 : Array Nat := #[0,2,34,66,97,114,146,178,210,241,259,308,370,401,417,434,465,481,498,530,563,610,643,690,722,753,769,785,801,817,834,865,881,897,915,963,1010,1043,1091,1138,1172,1235,1281,1299,1346,1379,1426,1459,1507,1557,1633,1650,1682,1716,1780,1843,1890,1922,1956,2017,2038,2132,2195,2241]
private def sixMenuStartsP1 : Array Nat := #[2257,2275,2324,2386,2420,2485,2565,2643,2689,2706,2739,2786,2818,2850,2884,2947,2995,3045,3124,3185,3201,3219,3266,3298,3330,3364,3427,3475,3522,3553,3570,3605,3684,3747,3793,3809,3826,3863,3971,4018,4052,4113,4131,4182,4275,4322,4353,4369,4386,4418,4450,4483,4530,4563,4613,4691,4739,4785,4802,4834,4866,4901,4980,5043]
private def sixMenuStartsP2 : Array Nat := #[5090,5126,5221,5300,5363,5410,5441,5459,5506,5540,5606,5700,5762,5796,5857,5878,5973,6050,6084,6147,6194,6225,6241,6257,6278,6369,6391,6501,6579,6626,6661,6743,6852,6916,6983,7089,7107,7153,7170,7206,7299,7347,7396,7460,7522,7554,7589,7667,7717,7796,7859,7907,7953,7970,8004,8066,8098,8130,8162,8193,8209,8225,8244,8305]
private def sixMenuStartsP3 : Array Nat := #[8321,8337,8354,8385,8403,8449,8466,8499,8547,8593,8612,8674,8709,8787,8835,8881,8902,8994,9025,9045,9122,9155,9203,9250,9285,9370,9521,9539,9586,9617,9636,9704,9828,9896,10021,10101,10180,10242,10274,10307,10357,10433,10452,10513,10530,10562,10595,10642,10676,10739,10785,10803,10851,10898,10931,10978,11010,11042,11075,11124,11185,11204,11267,11314]
private def sixMenuStartsP4 : Array Nat := #[11347,11395,11442,11474,11507,11553,11569,11585,11602,11634,11666,11697,11715,11763,11811,11857,11874,11906,11937,11953,11971,12017,12033,12050,12082,12114,12145,12162,12194,12225,12241,12258,12290,12323,12370,12402,12434,12466,12498,12531,12578,12609,12626,12658,12690,12721,12738,12770,12804,12868,12933,13011,13064,13186,13221,13298,13330,13363,13409,13427,13476,13541,13620,13684]
private def sixMenuStartsP5 : Array Nat := #[13749,13826,13858,13889,13910,14003,14050,14082,14115,14168,14292,14356,14420,14484,14553,14694,14792,14923,15095,15202,15237,15315,15364,15429,15508,15572,15634,15666,15698,15730,15762,15794,15826,15860,15923,15972,16037,16118,16211,16259,16306,16339,16388,16453,16533,16609,16627,16677,16756,16823,16934,17030,17124,17188,17250,17284,17347,17396,17458,17495,17602,17636,17704,17833]
private def sixMenuStartsP6 : Array Nat := #[17975,18084,18149,18231,18340,18402,18437,18515,18562,18597,18676,18740,18805,18884,18946,18981,19059,19109,19189,19265,19287,19395,19442,19479,19589,19667,19715,19766,19860,19927,20036,20098,20133,20210,20243,20291,20339,20387,20434,20472,20596,20662,20757,20834,20867,20917,20998,21092,21155,21207,21320,21445,21526,21623,21732,21797,21876,21942,22035,22085,22162,22200,22324,22388]
private def sixMenuStartsP7 : Array Nat := #[22450,22485,22570,22724,22788,22854,22949,23028,23090,23126,23219,23268,23332,23397,23474,23510,23613,23810,23841,23859,23908,23970,24006,24100,24164,24227,24275,24324,24387,24439,24548,24609,24626,24659,24712,24837,24916,24978,25010]
private def sixMenuStarts : Array (Array Nat) := #[sixMenuStartsP0,sixMenuStartsP1,sixMenuStartsP2,sixMenuStartsP3,sixMenuStartsP4,sixMenuStartsP5,sixMenuStartsP6,sixMenuStartsP7]
private def sixMenuWordsP0 : Array Nat := #[9,48,28,96,123,124,160,15,80,125,161,125,126,15,81,162,33,46,163,42,43,82,97,31,46,41,164,46,127,19,123,15,61,38,132,3,100,172,0,33,4,11,90,0,73,5,107,186,187,82,22,7,10,197,14,128,47,9,19,68,9,48,124,34]
private def sixMenuWordsP1 : Array Nat := #[69,19,28,83,19,20,68,19,35,1,12,20,35,1,28,34,21,9,31,48,28,129,1,19,20,1,9,1,19,35,9,48,130,1,12,35,70,71,9,1,12,21,48,69,129,131,166,9,14,24,38,9,80,128,24,49,15,167,14,15,20,168,17,15]
private def sixMenuWordsP2 : Array Nat := #[17,35,38,85,99,1,14,15,24,1,15,24,169,54,15,81,86,15,54,86,170,15,86,15,47,81,171,12,17,35,38,99,1,3,9,15,17,7,80,81,70,54,70,12,14,19,98,173,15,38,32,84,12,14,15,49,1,12,19,24,46,50,12,24]
private def sixMenuWordsP3 : Array Nat := #[46,50,101,1,33,39,102,11,55,41,44,50,55,89,88,104,55,138,0,1,11,174,11,33,39,51,55,103,11,55,39,42,43,0,4,17,87,90,12,44,51,88,54,139,175,34,130,91,105,4,8,13,25,33,37,56,8,25,37,8,56,20,41,141]
private def sixMenuWordsP4 : Array Nat := #[177,8,9,26,57,8,13,26,57,58,106,26,37,57,8,25,33,178,21,37,2,33,8,29,1,8,13,9,91,179,180,181,9,26,107,182,183,42,43,58,4,8,25,6,11,18,18,73,6,16,3,4,6,11,18,0,2,5,6,0,5,16,0,2]
private def sixMenuWordsP5 : Array Nat := #[0,2,3,5,6,10,0,2,3,10,11,0,5,73,143,30,63,71,74,184,185,42,43,188,8,14,8,14,45,109,3,8,14,40,45,75,11,14,18,76,18,31,6,16,20,31,48,6,9,20,31,33,39,0,3,4,6,26,2,48,14,20,52,76]
private def sixMenuWordsP6 : Array Nat := #[22,31,33,93,110,26,93,3,21,26,58,106,144,191,28,11,76,106,131,144,192,193,40,58,110,111,194,58,111,195,3,34,4,18,33,46,64,0,2,3,4,12,18,33,5,12,17,35,0,4,7,90,0,3,7,18,40,100,196,80,3,4,6,4]
private def sixMenuWordsP7 : Array Nat := #[1,90,2,4,5,82,97,100,2,3,10,0,10,198,1,4,6,22,6,55,64,86,17,36,6,43,0,3,4,82,97,8,13,29,8,14,25,45,65,2,8,13,29,8,13,23,13,25,29,108,5,147,8,13,27,36,32,200,3,32,2,87,8,112]
private def sixMenuWordsP8 : Array Nat := #[201,59,12,74,108,202,203,27,29,204,8,13,148,5,105,205,36,2,47,42,43,111,4,5,92,138,42,43,58,110,19,34,1,19,34,35,83,19,83,165,19,35,83,61,15,38,49,72,84,98,24,85,38,1,15,20,24,38,3,85,61,70,133,14]
private def sixMenuWordsP9 : Array Nat := #[15,20,1,133,12,15,19,72,98,1,12,15,28,33,61,87,101,134,135,44,4,50,62,4,62,43,0,47,50,72,11,15,61,87,88,96,101,103,96,104,136,137,0,28,33,44,61,88,134,135,0,54,89,126,137,0,47,54,72,89,4,42,62,104]
private def sixMenuWordsP10 : Array Nat := #[132,140,34,140,91,105,176,19,51,62,141,142,16,73,74,107,143,30,73,108,10,89,4,42,189,1,31,9,11,16,31,0,9,31,102,31,35,102,31,35,92,92,136,31,35,74,31,139,41,190,1,127,9,11,12,0,5,9,12,46,12,20,46,145]
private def sixMenuWordsP11 : Array Nat := #[12,20,146,20,64,2,64,84,29,84,199,50,206,13,50,51,142,148,113,77,1,9,32,14,34,1,7,15,1,12,38,3,9,32,12,24,49,24,0,39,12,51,20,13,8,23,119,5,0,5,120,5,63,5,121,213,10,12,2,16,10,154,2,17]
private def sixMenuWordsP12 : Array Nat := #[2,67,2,3,4,3,4,10,17,6,17,6,23,10,23,7,22,27,4,13,23,5,20,5,219,4,10,42,22,23,14,113,9,19,34,41,9,19,34,35,1,3,24,94,114,1,94,114,1,9,14,15,20,24,38,66,1,66,1,7,66,94,207,1]
private def sixMenuWordsP13 : Array Nat := #[15,11,24,11,115,116,208,0,34,117,0,14,115,118,11,12,24,51,117,11,12,78,118,0,12,34,51,0,12,14,78,116,13,95,13,57,91,3,4,11,23,25,59,3,4,18,1,13,14,20,14,103,113,8,11,13,14,23,25,69,112,9,13,21]
private def sixMenuWordsP14 : Array Nat := #[23,8,13,21,23,0,8,37,149,0,8,37,49,8,21,23,26,39,49,57,119,149,1,13,32,56,75,77,3,32,53,56,77,150,210,211,1,13,21,23,26,32,56,57,77,119,151,13,21,23,32,56,77,151,16,18,3,4,6,16,18,0,2,10]
private def sixMenuWordsP15 : Array Nat := #[2,5,6,10,2,3,5,6,10,2,5,10,16,2,3,10,16,6,120,30,121,16,120,30,71,16,63,30,44,1,30,0,2,5,16,2,44,79,0,2,5,30,0,2,5,71,153,0,2,5,23,30,63,1,66,212,1,10,66,5,45,5,9,17]
private def sixMenuWordsP16 : Array Nat := #[2,5,9,10,5,12,16,26,78,0,2,10,12,78,45,8,45,109,3,14,40,75,109,1,6,16,31,1,3,4,6,16,18,21,0,1,6,9,31,39,0,1,3,4,6,39,0,9,16,39,0,3,16,39,11,28,1,9,21,32,9,37,155,9]
private def sixMenuWordsP17 : Array Nat := #[12,29,37,28,29,1,13,21,28,29,37,57,28,79,8,28,29,34,3,4,11,21,26,40,52,60,3,4,11,14,26,28,40,52,76,1,2,3,5,18,45,46,1,5,17,64,1,2,4,7,53,1,3,5,9,17,18,40,2,3,6,11,1,53]
private def sixMenuWordsP18 : Array Nat := #[2,5,6,9,11,0,1,10,1,4,0,1,2,3,10,5,6,9,11,1,2,6,22,3,5,6,11,26,0,4,8,27,27,156,8,25,27,45,65,8,25,45,1,7,9,17,215,1,7,17,25,157,150,1,9,13,14,25,65,157,27,29,67,27]
private def sixMenuWordsP19 : Array Nat := #[29,7,13,25,27,29,36,45,5,17,32,95,147,13,25,27,3,4,32,4,23,25,32,53,59,1,4,32,69,0,4,7,40,53,59,69,4,8,23,112,4,114,2,4,10,24,27,4,24,59,94,156,1,12,59,1,10,32,10,52,216,36,53,0]
private def sixMenuWordsP20 : Array Nat := #[3,4,7,23,40,53,95,10,27,52,217,0,2,10,12,23,27,2,10,36,49,53,5,29,6,16,27,6,12,16,27,145,6,9,11,13,56,75,0,3,18,67,5,60,75,3,4,6,11,18,21,218,1,3,4,6,11,18,21,60,3,4,11,21]
private def sixMenuWordsP21 : Array Nat := #[40,0,3,7,13,18,40,0,1,3,7,18,40,67,0,4,7,13,0,2,5,6,10,0,3,5,16,0,2,5,6,10,115,2,5,13,0,2,10,11,116,2,28,5,6,12,13,27,39,117,146,0,2,5,28,0,2,11,220,2,60,3,4,6]
private def sixMenuWordsP22 : Array Nat := #[11,26,0,1,3,4,6,11,26,60,118,221,2,14,36,67,0,2,3,5,0,1,2,3,5,10,0,2,3,4,5,14,52,76,154,0,3,0,11,26,60,78,158,10,52,158,0,5,52,60,10,14,36,67,0,2,5,20,65,20,44,3,4,24]
private def sixMenuWordsP23 : Array Nat := #[62,68,85,8,13,19,23,24,34,38,51,62,68,72,99,209,30,152,79,63,74,153,8,9,28,37,32,37,8,9,12,28,29,37,9,29,37,152,41,79,155,214,0,4,5,5,8,27,3,4,25,27,9,13,25,9,12,23,25,27,29,65,9,13]
private def sixMenuWordsP24 : Array Nat := #[25,29,159,4,7,2,4,22,2,6,7,10,17,22,122,222,3,7,21,95,122,7,10,22,122,5,65,10,223]
private def sixMenuWords : Array (Array Nat) := #[sixMenuWordsP0,sixMenuWordsP1,sixMenuWordsP2,sixMenuWordsP3,sixMenuWordsP4,sixMenuWordsP5,sixMenuWordsP6,sixMenuWordsP7,sixMenuWordsP8,sixMenuWordsP9,sixMenuWordsP10,sixMenuWordsP11,sixMenuWordsP12,sixMenuWordsP13,sixMenuWordsP14,sixMenuWordsP15,sixMenuWordsP16,sixMenuWordsP17,sixMenuWordsP18,sixMenuWordsP19,sixMenuWordsP20,sixMenuWordsP21,sixMenuWordsP22,sixMenuWordsP23,sixMenuWordsP24]
private def sixMenuAtP0 : Array Nat := #[0,0,0,0,0,1,2,3,0,0,4,0,0,0,0,0,0,0,0,0,5,6,7,8,0,9,0,0,0,0,0,0,0,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP1 : Array Nat := #[11,0,0,0,0,0,0,0,0,0,12,0,13,13,0,14,15,0,0,0,0,16,17,18,19,20,0,21,22,0,0,23,0,0,0,0,24,0,0,25,26,0,0,0,0,0,0,0,0,27,28,29,30,28,29,0,0,0,0,0,0,0,0,31]
private def sixMenuAtP2 : Array Nat := #[32,0,0,0,0,31,0,0,0,0,33,0,0,0,34,35,36,0,0,37,38,39,0,40,0,41,13,0,0,42,0,43,44,38,45,0,46,47,48,49,0,0,42,42,0,50,51,52,53,0,54,55,56,56,0,0,57,58,0,59,0,60,61,62]
private def sixMenuAtP3 : Array Nat := #[0,63,64,0,0,0,0,0,0,29,0,65,66,67,68,0,0,29,29,0,59,59,59,69,0,0,70,71,72,73,74,75,76,77,78,79,80,81,82,0,0,0,0,0,0,83,0,0,0,0,0,0,84,85,0,0,85,0,86,87,88,89,90,91]
private def sixMenuAtP4 : Array Nat := #[92,0,0,0,21,0,93,94,0,95,96,0,0,0,0,59,97,0,0,0,0,0,0,0,0,0,98,0,0,0,99,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,29,29,0,0,101,102,103,104,0,0,0,0,93,0,0,0,0]
private def sixMenuAtP5 : Array Nat := #[105,33,106,107,108,109,0,0,0,0,29,29,29,0,110,111,112,113,114,105,115,105,116,117,0,118,119,120,121,122,123,124,125,126,127,128,129,130,128,131,0,132,133,0,0,134,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,110]
private def sixMenuAtP6 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,135,0,0,105,136,0,137,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,138,0]
private def sixMenuAtP7 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,139,140,141,125,142,28,143,144,145,146,147,142,148,0,149,149,0,149,149,150,150,150,151,152,153,0,154,155,156,157,158,159,160,161,0,0,121,0,121,121,162,163,28,0,0,0,164]
private def sixMenuAtP8 : Array Nat := #[165,0,166,0,167,0,0,168,169,170,171,172,173,174,0,175,176,177,0,0,0,0,29,172,0,29,29,178,179,180,181,182,183,184,0,0,0,0,185,186,0,0,0,0,0,0,0,0,187,0,0,188,189,0,0,190,191,192,193,0,194,33,119,195]
private def sixMenuAtP9 : Array Nat := #[0,0,0,0,0,0,196,0,197,0,0,0,198,199,200,201,94,202,197,0,42,0,0,0,0,0,0,0,0,0,0,0,0,203,16,204,205,206,207,208,209,210,211,76,72,212,213,214,0,215,0,216,217,218,219,218,64,0,220,221,222,223,224,225]
private def sixMenuAtP10 : Array Nat := #[226,227,228,229,230,231,0,232,0,121,0,0,233,0,0,0,0,234,0,0,235,0,0,0,236,0,0,33,221,33,237,238,239,240,241,242,243,0,13,244,245,13,246,244,247,0,248,249,250,251,252,253,254,255,255,256,257,0,0,258,259,0,260,0]
private def sixMenuAtP11 : Array Nat := #[0,0,0,0,261,0,0,0,0,0,0,262,0,0,0,0,0,16,263,264,265,0,266,0,267,0,268,269,270,271,0,0,0,0,0,0,84,0,272,0,273,0,83,0,0,0,0,0,0,0,274,0,0,0,0,0,29,0,0,0,105,105,275,276]
private def sixMenuAtP12 : Array Nat := #[0,0,29,29,0,0,105,0,105,0,277,0,168,0,0,0,0,0,0,278,0,0,0,279,0,0,0,0,0,0,0,0,0,0,0,0,0,0,280,0,0,0,0,0,0,0,281,0,0,0,0,0,0,263,263,282,0,283,0,284,0,0,285,0]
private def sixMenuAtP13 : Array Nat := #[0,0,0,286,0,0,287,285,0,284,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,287,0,0]
private def sixMenuAtP14 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,288,0,0,0,0,0,0,0,0,0,0,151,0,0,0,0,0,0,0,0,153,0,121,28,289,29,0,121,28,290,29,291,292,28,28,28,0,0,293,0,0,29,29,29,0,0,0,294,0,0,295,296,0,0]
private def sixMenuAtP15 : Array Nat := #[0,0,0,275,297,0,0,298,299,0,0,197,0,300,0,0,0,0,0,0,0,301,197,0,300,0,0,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP16 : Array Nat := #[0,0,0,0,0,0,0,302,0,0,0,0,0,0,0,303,304,0,305,0,306,29,307,308,29,309,310,311,0,0,312,313,314,315,316,189,317,318,319,320,0,321,0,0,0,151,322,0,0,323,0,0,324,0,325,0,29,0,189,326,327,328,0,329]
private def sixMenuAtP17 : Array Nat := #[0,330,331,0,29,0,332,333,334,105,335,336,337,338,121,339,124,340,341,342,343,344,345,346,347,235,348,349,347,350,0,124,351,0,0,132,0,275,0,235,352,0,0,0,0,0,341,126,353,128,354,128,0,0,128,355,0,0,0,0,356,0,355,357]
private def sixMenuAtP18 : Array Nat := #[0,0,0,358,309,359,0,360,361,0,0,362,0,363,364,0,0,0,365,105,136,105,0,105,0,0,366,0,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,367,0,0,0,0,0,0,0,0]
private def sixMenuAtP19 : Array Nat := #[0,0,339,368,369,370,371,372,373,374,375,376,0,0,377,0,0,378,379,0,0,0,380,381,0,382,383,384,385,386,387,0,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,197,403,404,29,172,29,405,406,407,408,409,410,0,0,28,28,411]
private def sixMenuAtP20 : Array Nat := #[412,413,414,121,0,0,0,0,28,415,0,0,416,417,418,419,29,0,29,420,421,422,423,424,425,426,427,165,428,429,125,430,431,432,433,434,435,436,437,438,0,0,0,439,440,129,130,441,442,443,444,445,0,446,447,448,449,450,451,452,453,454,455,456]
private def sixMenuAtP21 : Array Nat := #[457,458,459,460,0,461,0,0,0,0,0,0,0,0,0,0,0,0,462,463,464,351,351,235,465,466,467,468,469,470,471,466,472,473,474,475,476,477,478,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP22 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,31,0,0,0,0,0,0,128,0,128,0,0,479,0,0,0,0,0,0,0,479,0,0,0,0]
private def sixMenuAtP23 : Array Nat := #[0,0,0,0,0,0,0,0,188,266,28,480,0,481,29,263,482,0,0,483,0,277,277,0,151,0,0,0,484,0,0,0,0,0,0,0,277,485,0,0,486,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAt : Array (Array Nat) := #[sixMenuAtP0,sixMenuAtP1,sixMenuAtP2,sixMenuAtP3,sixMenuAtP4,sixMenuAtP5,sixMenuAtP6,sixMenuAtP7,sixMenuAtP8,sixMenuAtP9,sixMenuAtP10,sixMenuAtP11,sixMenuAtP12,sixMenuAtP13,sixMenuAtP14,sixMenuAtP15,sixMenuAtP16,sixMenuAtP17,sixMenuAtP18,sixMenuAtP19,sixMenuAtP20,sixMenuAtP21,sixMenuAtP22,sixMenuAtP23]
private def atSix (v : Array (Array Nat)) (i : Nat) : Nat := ((v[i/64]?).getD #[])[i%64]?.getD 0
private def sixOffset : Nat → Nat
  | 6 => 0
  | 7 => 2
  | 8 => 81
  | 9 => 703
  | 10 => 1383
  | 11 => 1515
  | 12 => 1525
  | _ => 0
private def inlineMenu (m k i : Nat) : List Nat :=
  if m=251 then
    let mnum := atSix sixMenuAt (sixOffset k+i)
    let offsetCode := atSix sixMenuStarts mnum
    (List.range (offsetCode % 16)).map (fun j => atSix sixWords (atSix sixMenuWords (offsetCode / 16 + j)))
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

def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[5,6]⟩,⟨.or,[1,3]⟩,⟨.or,[2,4]⟩,⟨.or,[4,8]⟩,⟨.or,[1,7]⟩,⟨.or,[5,7]⟩,⟨.or,[3,7]⟩,⟨.or,[8,14]⟩,⟨.and,[15,0]⟩,⟨.and,[13,9]⟩,⟨.and,[12,11]⟩,⟨.and,[6,10]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 6, 0, 1, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 6, 0, 1, 0, 0, 0] : List Nat).getD i.val 0))

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
def K41 := extendKnown [] 4 [(41,[]),(82,[16,67,101]),(137,[117,101]),(146,[16,67,117,101]),(161,[83,67,116,100]),(162,[16,83,67,116,100]),(168,[48,16,33,82,66,116,100]),(193,[99,67,117]),(194,[16,99,67,117]),(208,[64,16,33,99,117])]
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
def K43 := extendKnown K41 5 [(43,[]),(83,[16,67,101]),(105,[48,97,33,80,66]),(114,[64,81,32,99]),(139,[117,101]),(147,[16,67,117,101]),(153,[65,33,117,101]),(154,[16,48,32,66,117,101]),(177,[65,33,83,115,99]),(184,[48,65,32,82,114,98]),(202,[16,48,32,98,66,117]),(216,[64,49,32,97,33,117]),(232,[48,97,32,82,65,114,66]),(240,[64,81,32,99,33,114,50])]
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
def K51 := extendKnown K43 4 [(51,[]),(58,[48,32]),(75,[16,67,101]),(89,[48,97,33,32,80]),(106,[48,32,100]),(113,[64,16,33,50,83,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V51 : Known true K51 := extend_ok (m:=51) V43 low51 (by decide +kernel)
def g163Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0)]
def g163C : List ColumnInfo := [(1,0,162,0,4)]
def g163A : List (List Nat) := [[],[117],[16],[16,117]]
def g163D4 (j : Nat) := if j=0 then 0x1f else 0
def g163L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g163D4)
  | _ => emptyPacking
def g163I (_ _ : Nat) : Option (Nat × Nat) := none
def g163 : Forest := ⟨163,4,fun i => g163Y[i]?.getD (0,0),g163C,g163A,g163L,g163I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g163P4_0 : block g163 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g163B4 : block g163 4 0 1=true := g163P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g163T : checkedTables g163 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g163 0 0 0 = true)
  · exact (rfl : block g163 1 0 0 = true)
  · exact (rfl : block g163 2 0 0 = true)
  · exact (rfl : block g163 3 0 0 = true)
  · exact g163B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g163G : graphValid g163 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low163 : Lower true (varsX 163) (graphGoal 163) 5 := lower_forest (g:=g163) (i:=0) (hints:=85) (before_sound K51 V51) g163G g163T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K163 := extendKnown K51 5 [(163,[]),(170,[16,48,32]),(178,[64,81,32,50]),(195,[101]),(201,[48,97,33,32,80]),(225,[80,97,33,50,67]),(226,[80,97,32,50,67,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V163 : Known true K163 := extend_ok (m:=163) V51 low163 (by decide +kernel)
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
theorem g169G : graphValid g169 (boundsBefore K163) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low169 : Lower true (varsX 169) (graphGoal 169) 7 := lower_forest (g:=g169) (i:=0) (hints:=3) (before_sound K163 V163) g169G g169T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K169 := extendKnown K163 7 [(169,[]),(210,[16,67,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V169 : Known true K169 := extend_ok (m:=169) V163 low169 (by decide +kernel)
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
def K59 := extendKnown K169 7 [(59,[]),(91,[16,67,101]),(121,[48,97,33,80]),(122,[64,81,32,99,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V169 low59 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff00ffffc3fff007fe,0x1ff0fffff85e060f00ff])),(BitVec.ofNat 152 (word80 [0xa0a05008800a05014,0x40220020980602111111]))),((BitVec.ofNat 152 (word80 [0xffff007ffc3ffff800,0x1fff0ff01cb4b9f00f00])),(BitVec.ofNat 152 (word80 [0x2c0c16050082c06058,0x81402042189431333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff80003fffffff,0xe0000fff23b56600f00f])),(BitVec.ofNat 152 (word80 [0x301018261113048260,0x984448021b064666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffff,0xfffff000134bf800fff0])),(BitVec.ofNat 152 (word80 [0x40a0a0482224090480,0x12000904024988888888]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0xcea8c5ff0000])),(BitVec.ofNat 152 (word80 [0x80c0c07000380e0701,0x1c088e084628c4cccccc]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(2,0,105,0,5)]
def g107A : List (List Nat) := [[],[80,97]]
def g107D5 (j : Nat) := if j=0 then 0x3f else 0
def g107L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g107D5)
  | _ => emptyPacking
def g107I (_ _ : Nat) : Option (Nat × Nat) := none
def g107 : Forest := ⟨107,5,fun i => g107Y[i]?.getD (0,0),g107C,g107A,g107L,g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P5_0 : block g107 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B5 : block g107 5 0 1=true := g107P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : checkedTables g107 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g107 0 0 0 = true)
  · exact (rfl : block g107 1 0 0 = true)
  · exact (rfl : block g107 2 0 0 = true)
  · exact (rfl : block g107 3 0 0 = true)
  · exact (rfl : block g107 4 0 0 = true)
  · exact g107B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 6 := lower_forest (g:=g107) (i:=0) (hints:=83) (before_sound K59 V59) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K59 6 [(107,[]),(115,[16,67,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V59 low107 (by decide +kernel)
def g155Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff87fc3fff00,0xffff1ffed2e680007c1f])),(BitVec.ofNat 152 (word80 [0x222894451108808a4a,0xa02444252268a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (word80 [0x40b018162050082c0c,0x2c140089146346318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c120980261113010,0x30588900a8d154a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c0e0438221c060,0x40600e104b9898c6318c]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80201000400020080,0x80801000000021084210]))),(0x0,0x0)]
def g155C : List ColumnInfo := [(1,0,154,0,5),(2,0,153,0,5),(8,0,147,0,5),(16,0,139,0,5),(9,0,146,0,4),(18,0,137,0,4)]
def g155A : List (List Nat) := [[],[65],[16,67],[16,48,64],[48],[48,65],[64,16,49],[64,49]]
def g155D4 := limbs80 #[#[0x9bd89544426d6215110,0x31825f635474]]
def g155D5 := limbs80 #[#[0x3527f7bbf6f4050110,0x5f405d50654155045435,0x66ad0941001546b525d4,0xc08024050462b13e3bb,0x4040201642000001201]]
def g155H5 (j : Nat) := if j=0 then 0x10240028000c40032 else 0
def g155D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x3140cc503]]
def g155H6 := limbs80 #[#[0x800000000c241,0x84001100c90046004700,0x970000000000008543d9,0x54002100000000009300]]
def g155D7 (j : Nat) := if j=0 then 0x1605f else 0
def g155H7 := limbs80 #[#[0x116007402129320006,0xca00002518ea]]
def g155L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g155D4)
  | 5 => (10,2,3,262147,34,7,1030,g155D5)
  | 6 => (3,1,3,0,0,6,0,g155D6)
  | 7 => (1,0,3,0,0,0,0,g155D7)
  | _ => emptyPacking
def g155I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 11 0 6 2 2 g155H5
  | 6 => lookupShort 4 41 0 8 4 2 g155H6
  | 7 => lookupShort 3 19 1 7 2 3 g155H7
  | _ => fun _ => none
def g155 : Forest := ⟨155,7,fun i => g155Y[i]?.getD (0,0),g155C,g155A,g155L,g155I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P4_0 : block g155 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B4 : block g155 4 0 3=true := g155P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P5_0 : block g155 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P5_1 : block g155 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B5 : block g155 5 0 10=true := (@block_merge g155 5 0 1 9 g155P5_0 g155P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P6_0 : block g155 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B6 : block g155 6 0 3=true := g155P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P7_0 : block g155 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B7 : block g155 7 0 1=true := g155P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155T : checkedTables g155 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g155 0 0 0 = true)
  · exact (rfl : block g155 1 0 0 = true)
  · exact (rfl : block g155 2 0 0 = true)
  · exact (rfl : block g155 3 0 0 = true)
  · exact g155B4
  · exact g155B5
  · exact g155B6
  · exact g155B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155G : graphValid g155 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 8 := lower_forest (g:=g155) (i:=0) (hints:=65603) (before_sound K107 V107) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K107 8 [(155,[]),(248,[48,65,32,82,97,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V107 low155 (by decide +kernel)
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
theorem g171G : graphValid g171 (boundsBefore K155) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 8 := lower_forest (g:=g171) (i:=0) (hints:=83) (before_sound K155 V155) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K155 8 [(171,[]),(233,[48,97,33,80,66]),(242,[64,81,32,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V155 low171 (by decide +kernel)
def g179Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff007f87f87ffc0,0x3fff8ffc48be5000f0f0])),(BitVec.ofNat 152 (word80 [0x5442a1505109100a8a,0x85092009489a53333333]))),((BitVec.ofNat 152 (word80 [0x1ffff8007ff87fff,0xc07ff1ffbb19600f0f0f])),(BitVec.ofNat 152 (word80 [0x1880c0606202010303,0x6020410290941111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xff8001ff941fb0f0000f])),(BitVec.ofNat 152 (word80 [0x610b0582802c222c0c,0x82c48a01416b6666666]))),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06030430443010,0x103000c20264a4444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008040040004020,0x20400100000008888888]))),(0x0,0x0)]
def g179C : List ColumnInfo := [(1,0,178,0,5),(2,0,177,0,5),(16,0,163,0,5),(32,0,147,0,5)]
def g179A : List (List Nat) := [[],[64,81]]
def g179D6 (j : Nat) := if j=0 then 0x4689f else 0
def g179L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g179D6)
  | _ => emptyPacking
def g179I (_ _ : Nat) : Option (Nat × Nat) := none
def g179 : Forest := ⟨179,6,fun i => g179Y[i]?.getD (0,0),g179C,g179A,g179L,g179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P6_0 : block g179 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B6 : block g179 6 0 1=true := g179P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179T : checkedTables g179 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g179 0 0 0 = true)
  · exact (rfl : block g179 1 0 0 = true)
  · exact (rfl : block g179 2 0 0 = true)
  · exact (rfl : block g179 3 0 0 = true)
  · exact (rfl : block g179 4 0 0 = true)
  · exact (rfl : block g179 5 0 0 = true)
  · exact g179B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 7 := lower_forest (g:=g179) (i:=0) (hints:=65605) (before_sound K171 V171) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K179 := extendKnown K171 7 [(179,[]),(186,[48,32]),(203,[16,67,101]),(217,[48,97,33,32,80]),(234,[48,32,100]),(241,[64,16,33,50,83,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V171 low179 (by decide +kernel)
def g185Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff0ff87ffc0,0x7fff8fffdcb91000f0ff])),(BitVec.ofNat 152 (word80 [0x244121202209100489,0x20920084c8901111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffff000fff87fff,0x80fff1ffb31f200f0f0f])),(BitVec.ofNat 152 (word80 [0x488240414412010902,0x14120410311602222222]))),((BitVec.ofNat 152 (word80 [0x1fffffff00007fff,0xff0001fc0c1ef0f00000])),(BitVec.ofNat 152 (word80 [0x710b8585805c222e0c,0x185c48a10c1ef7777777]))),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060860443010,0x206000c20260b4444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080080004020,0x40800100000008888888]))),(0x0,0x0)]
def g185C : List ColumnInfo := [(16,0,169,0,7)]
def g185A : List (List Nat) := [[],[83],[48],[48,80],[80,48],[80]]
def g185D7 (j : Nat) := if j=0 then 0x3f else 0
def g185L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g185D7)
  | _ => emptyPacking
def g185I (_ _ : Nat) : Option (Nat × Nat) := none
def g185 : Forest := ⟨185,7,fun i => g185Y[i]?.getD (0,0),g185C,g185A,g185L,g185I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185P7_0 : block g185 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g185B7 : block g185 7 0 1=true := g185P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185T : checkedTables g185 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g185 0 0 0 = true)
  · exact (rfl : block g185 1 0 0 = true)
  · exact (rfl : block g185 2 0 0 = true)
  · exact (rfl : block g185 3 0 0 = true)
  · exact (rfl : block g185 4 0 0 = true)
  · exact (rfl : block g185 5 0 0 = true)
  · exact (rfl : block g185 6 0 0 = true)
  · exact g185B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185G : graphValid g185 (boundsBefore K179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low185 : Lower true (varsX 185) (graphGoal 185) 8 := lower_forest (g:=g185) (i:=0) (hints:=458755) (before_sound K179 V179) g185G g185T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K185 := extendKnown K179 8 [(185,[]),(218,[16,67,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V185 : Known true K185 := extend_ok (m:=185) V179 low185 (by decide +kernel)
def g227Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fe1fe01fe1fc3ffc,0x7ffe3ff1ecd460071c7])),(BitVec.ofNat 152 (word80 [0x141441414144088028,0x50a04802424506249249]))),((BitVec.ofNat 152 (word80 [0xfe001fffe001ffc3ff,0xf80ffc7fe17493038e38])),(BitVec.ofNat 152 (word80 [0x181881818188100830,0x60c08104095412249249]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffffe0003ff,0xfff0007ffcc2f51c003f])),(BitVec.ofNat 152 (word80 [0xa0a10a0a0a00a11140,0x810512280082e1492492]))),((BitVec.ofNat 152 (word80 [0xffffe00000000003ff,0xffffff80003b4be00fc0])),(BitVec.ofNat 152 (word80 [0xc0c00c0c0c10c22181,0x2060030902a49492492]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffc00,0x30628fff000])),(BitVec.ofNat 152 (word80 [0x10010101001000202,0x4080040000000924924]))),(0x0,0x0)]
def g227C : List ColumnInfo := [(1,0,226,0,5)]
def g227A : List (List Nat) := [[],[101],[16],[16,101],[80,97],[80,97,16],[96,81,16],[96,81]]
def g227D5 (j : Nat) := if j=0 then 0x3f else 0
def g227L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g227D5)
  | _ => emptyPacking
def g227I (_ _ : Nat) : Option (Nat × Nat) := none
def g227 : Forest := ⟨227,5,fun i => g227Y[i]?.getD (0,0),g227C,g227A,g227L,g227I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P5_0 : block g227 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B5 : block g227 5 0 1=true := g227P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227T : checkedTables g227 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g227 0 0 0 = true)
  · exact (rfl : block g227 1 0 0 = true)
  · exact (rfl : block g227 2 0 0 = true)
  · exact (rfl : block g227 3 0 0 = true)
  · exact (rfl : block g227 4 0 0 = true)
  · exact g227B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227G : graphValid g227 (boundsBefore K185) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low227 : Lower true (varsX 227) (graphGoal 227) 6 := lower_forest (g:=g227) (i:=0) (hints:=85) (before_sound K185 V185) g227G g227T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K227 := extendKnown K185 6 [(227,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V227 : Known true K227 := extend_ok (m:=227) V185 low227 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff72ac9,0x182ea80003f8001fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044032080,0x180ca80a142850a14285]))),((BitVec.ofNat 152 (word80 [0xfc003ffffffe03d528,0x15d8c201fc000fe03f80])),(BitVec.ofNat 152 (word80 [0x300b00500008235028,0x150840060c183060c183]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0001ffffad8ce,0x83211e000007f000007f])),(BitVec.ofNat 152 (word80 [0x410c1160889000d84e,0x81201654a952a54a952a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000804f6,0x691ab3fe000000003f80])),(BitVec.ofNat 152 (word80 [0x8050058002e04804c4,0x2812b33870e1c3870e1c]))),((BitVec.ofNat 152 (word80 [0x91711,0xa28774000007ffffc000])),(BitVec.ofNat 152 (word80 [0x26026011300880711,0x228300a142850a142850]))),((BitVec.ofNat 152 (word80 [0x4e917,0x7e4005fffff800000000])),(BitVec.ofNat 152 (word80 [0x38038021c01048913,0x424004c183060c183060]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(1,0,122,0,7),(2,0,121,0,7),(32,0,91,0,7),(64,0,59,0,7),(0,8,82,33,6),(8,0,115,0,6)]
def g123A : List (List Nat) := [[],[16,67,101],[80,97],[96,81,67]]
def g123D8 (j : Nat) := if j=0 then 0x2c6881bf else 0
def g123L : Nat → Packing
  | 8 => (1,0,3,0,0,0,0,g123D8)
  | _ => emptyPacking
def g123I (_ _ : Nat) : Option (Nat × Nat) := none
def g123 : Forest := ⟨123,8,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8_0 : block g123 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B8 : block g123 8 0 1=true := g123P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0 = true)
  · exact (rfl : block g123 1 0 0 = true)
  · exact (rfl : block g123 2 0 0 = true)
  · exact (rfl : block g123 3 0 0 = true)
  · exact (rfl : block g123 4 0 0 = true)
  · exact (rfl : block g123 5 0 0 = true)
  · exact (rfl : block g123 6 0 0 = true)
  · exact (rfl : block g123 7 0 0 = true)
  · exact g123B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K227) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 9 := lower_forest (g:=g123) (i:=0) (hints:=65603) (before_sound K227 V227) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K227 9 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V227 low123 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff801ffffe1fff9ae2,0x181cf000000fc003f03f])),(BitVec.ofNat 152 (word80 [0x450940500441101ac2,0x800f145145145145145]))),((BitVec.ofNat 152 (word80 [0xffffe007fffff8390b,0xb483500003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x160181602800213803,0xb40140c30c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff8001fffd03d,0x39712000fc003f00003f])),(BitVec.ofNat 152 (word80 [0x98020180b082400039,0x3171028a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8bc7903f000000000fc0])),(BitVec.ofNat 152 (word80 [0xe02c0a02c00b824628,0xbc6971c71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x4984,0x67ac8fc000003ffff000])),(BitVec.ofNat 152 (word80 [0x300c03010c044104,0x428c0410410410410410]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x4010040010000000,0x820820820820820]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(2,0,185,0,8),(16,0,171,0,8),(32,0,155,0,8),(1,0,186,0,7),(8,0,179,0,7),(128,0,59,0,7),(9,0,178,0,5),(129,0,58,0,4),(136,0,51,0,4)]
def g187A : List (List Nat) := [[],[48]]
def g187D6 := limbs80 #[#[0xe3c1243e437695254120,0x5]]
def g187D7 := limbs80 #[#[0xf54950bf59520fe54120,0x42a00ff58950bfd8950d,0xc32187c70572186ae8a5,0x481c5c705328c82071b1,0x81c60d4c70c871]]
def g187H7 (j : Nat) := if j=0 then 0x8 else 0
def g187D8 := limbs80 #[#[0xa38c2461a403faa1fd20,0x1e851c6121c]]
def g187H8 (j : Nat) := if j=0 then 0x18010032003021100 else 0
def g187D9 (j : Nat) := if j=0 then 0x5431021bf else 0
def g187H9 (j : Nat) := if j=0 then 0xb0000001000000 else 0
def g187L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g187D6)
  | 7 => (5,2,4,0,0,8,0,g187D7)
  | 8 => (2,1,4,0,0,6,0,g187D8)
  | 9 => (1,0,4,0,0,0,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupShort 1 2 0 2 0 0 g187H7
  | 8 => lookupShort 1 11 0 6 3 1 g187H8
  | 9 => lookupShort 1 17 0 4 1 1 g187H9
  | _ => fun _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_0 : block g187 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B6 : block g187 6 0 1=true := g187P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_4 : block g187 7 4 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B7 : block g187 7 0 5=true := (@block_merge g187 7 0 4 1 g187P7_0 g187P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : block g187 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B8 : block g187 8 0 2=true := g187P8_0
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
  · exact (rfl : block g187 5 0 0 = true)
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
def K187 := extendKnown K123 10 [(187,[]),(219,[16,67,101]),(249,[48,97,33,80]),(250,[64,81,32,99,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V123 low187 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff003ff87fe1fffffa,0x261b1000007c1f003ff])),(BitVec.ofNat 152 (word80 [0xa02805100440020da,0x2011004210842108421]))),((BitVec.ofNat 152 (word80 [0xffffc0007ffe1ff05d,0x3ccb008000f83e007c00])),(BitVec.ofNat 152 (word80 [0x2c0301620280404259,0x3c43000c6318c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff80001fff20,0xf4791e001f00000f801f])),(BitVec.ofNat 152 (word80 [0x302409801308848020,0xf4780218c6318c6318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffe00010,0xab842f83e000000fffe0])),(BitVec.ofNat 152 (word80 [0x404812002400090400,0x1842da1084210842108]))),((BitVec.ofNat 152 (word80 [0xe,0x11bac77c00003ff00000])),(BitVec.ofNat 152 (word80 [0x80701c0438110e0804,0x1b8c7318c6318c6318c]))),((BitVec.ofNat 152 (word80 [0xc1,0x4514407fffffc0000000])),(BitVec.ofNat 152 (word80 [0x8020004000100000,0x42108421084210]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(2,0,233,0,8),(64,0,171,0,8),(1,0,234,0,7),(32,0,203,0,7),(66,0,169,0,7),(8,0,227,0,6),(128,0,107,0,6),(3,0,232,0,5),(9,0,226,0,5),(10,0,225,0,5),(33,0,202,0,5),(34,0,201,0,5),(40,0,195,0,5),(65,0,170,0,5),(96,0,139,0,5),(130,0,105,0,5),(192,0,43,0,5),(41,0,194,0,4),(67,0,168,0,4),(98,0,137,0,4),(129,0,106,0,4),(160,0,75,0,4)]
def g235A : List (List Nat) := [[],[80,97]]
def g235D4 := limbs80 #[#[0x9822139398595434c110,0x7550d30442b232f32a86,0x89caac6a1aa088760e49,0x822171193a154354110b,0x750d50442b2726c3a86a,0x81c6564cb0c056464e8,0x5282000014a094a]]
def g235D5 := limbs80 #[#[0x4c11054d30441434c110,0x442654c1105d53044165,0x995434417050d1059543,0x54110549504414354110,0x44163541105895044153,0xdd95244176549105cd50,0x54d105d9534416354d10,0x4437459510dd95344265,0x5db5244265c811059720,0xb727c9e6759b576d4d10,0xe5778db364be2f4bb2e5,0x9a12ba83e4f63d4f33c4,0x3d90c158dc2551c155aa,0x285eb286332822b2806c,0x390ec190dc208fc189f3,0x9a09c2ae0b1257c10c6c,0x2a1cc2a22b9a22b1a22a,0x2b1eb1a9543a14c3a1d4,0x2383c1b87c0391c1349c,0x2994ba981c25c6c03c1c,0x2c0ac19ccc01c1c394dc,0x2445c1447c0448c0498b,0xc1d01c2606c04c1c,0x2b12c803416090381406,0xac5026114803b1b8cc5e,0x2f0f83bf1e8e36db2d76,0xa6c359a6512792f93c7e,0x3eaf4799c8e270379b8d,0x805e0a042e0889846254,0x19083400a5400c0148,0xc050159080000000,0x116a0801a4480a020000],#[0x908001d08026108bc8ae,0xb0800065840000000002,0x1010000000000000000e]]
def g235H5 := limbs80 #[#[0xb9d03c4fb014000000,0x8400000000000004850,0x3600]]
def g235D6 := limbs80 #[#[0x549105411050d104c110,0x5951058d105891054d10,0xd4d10d4910c811099510,0x54130595205492054120,0xedb3b58d505495059530,0x76badbedeeeefd7dbe5e,0xfb7d7e9edf6793bdddee,0x9a2a4972860fe7ebf3f8,0x25aa421aea08aa601aea,0x25ea625aa627a8625ea4,0xb7ae011ae0a1ee031ee6,0xf52a4c1ae080ee871ae0,0xbcca9baca906e504aa6,0x2bac42baa42bcca0baca,0x3bae62bac62baa62bae4,0xa26ec322ec3aac43bee0,0x182ca126ea53aca522ec,0x492c64bae0482ec184ca,0xb26ec422ec464ca462ca,0x726ea63aca622ecb62ca,0x822e4886e8726e6726e4,0xf46e0eb6e0db2a4c22e6,0x26ee112ee1136e509aa6,0xb1784b1002d0640016e5,0x2358c32c4a42608b1dc6,0xd5fd6b565414a51a414f,0xb819f2781d26f9b06858,0xa367c9a65a94a438ba1,0xcc5305bf6efb7ac8ac6a,0x4e1f75d9355d0f37ca31,0xffcbe5f5fcaef3aee879,0x8848c943c50981f8447f],#[0xc2c202708b0b98418000,0x3510142a0b823d1e121,0x126a8e1104c493d0b0f0,0x88047d80800ef911df1,0x7811a0100110093b0860,0xeb1bf40491238457e808,0xb16d60226d60222904cc,0x8c911c4925245612499e,0xc4436e188b611c443348,0x2e45a3e430f8c5d18639,0x93ab14ad0a0f219b2200,0x53e429ac50c231b1d798,0xa826c8ac840239100564,0x68350b106c8ed910d685,0x303b412d86981da0ad05,0x1b419a0d]]
def g235H6 := limbs80 #[#[0x10802013c08232b20,0xb00000ea8020000000,0x594138001ed3e5c010d7,0xe000021d030a88948c20,0xc01a90000056a50d003a,0x409f000008e83c968,0x69809aa4a8000089cc,0x994e86c0000001524800,0xa98001d,0x1a20022e0c0000000,0x78034356c9800291c000,0x196067192182c]]
def g235D7 := limbs80 #[#[0xc8252549504c12044052,0xcfbeddfdbbfbebdd4b50,0xd50174c05f201fffefdf,0x84f526058405600550c5,0xd4c61531858863521854,0x29540a26518594616318,0x5032595d952725949952,0xb6244d49115242594e5,0x8a115282d8d13534454d,0x2582496562d814963825,0x5a58d29534a58929524,0xc490c42205000ad81696,0x4dc32cba284901fc6d16,0x5715794b4fd32499103d,0x5e4761cb6ddab679915f,0x657926358a21682dfe7c,0x10038629808e1a367f9a,0x8574758152a32b086261,0x15c03bcc23442878b12,0xd608b7022d608179c4a5,0xa7014f9a04a9c054e02a,0xe05b96184d7cd0254e02,0xe810f9028022010010ed,0x3002201000afe00a0087,0xa0110088040044023f00,0x1da456ca488045a81401,0xd62876914f6c881e9]]
def g235H7 := limbs80 #[#[0x200f0130340020208180,0x26082760801838c0f0,0xdc000f33003528c5d865,0x8b6c8e008f251270757a,0x40d46f9ab490001ca2c5,0x1848ba376b92cf8fa73c,0x703a292428013ccc0866,0x5b74a715ef61d2d9524,0x446cd470200003500064,0xb60e0ca124e000e35dc3,0x92c55070605c15d1]]
def g235D8 := limbs80 #[#[0xea154298720a40443ffd,0x72b1d1100ea594aa9452,0x30244682184756956493,0x84028021981435001c8,0xc0280238807002bc00c0,0x10]]
def g235H8 := limbs80 #[#[0x422018400020100021,0x300000000045e302e000,0x6000000000a4528031f1,0x10c0062000ac00820014,0xd20000,0x1218500030c800,0x50201960053b280109,0x7c38000000000,0x59c50300000018200000,0x742cea600074a908000,0x19800008d00000000,0x1500234000000000000,0x98fd700047b400005140,0x664001408000830e0007,0xdf0066fa2a200,0x7840092000000000,0x15c8380000000020400,0x8500000000000000]]
def g235D9 (j : Nat) := if j=0 then 0x1882013f else 0
def g235H9 := limbs80 #[#[0x45000000000000024020,0x4e821040000300420005,0x2400000000100000051,0x11405586000000]]
def g235L : Nat → Packing
  | 4 => (7,5,5,0,0,6,0,g235D4)
  | 5 => (45,4,5,1179673,85,9,1040,g235D5)
  | 6 => (63,3,5,1572883,85,10,1059,g235D6)
  | 7 => (40,2,5,720906,68,10,1048,g235D7)
  | 8 => (10,1,5,131073,16,8,1035,g235D8)
  | 9 => (1,0,5,0,0,0,0,g235D9)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 2 29 0 6 3 1 g235H5
  | 6 => lookupShort 14 97 4 9 6 1 g235H6
  | 7 => lookupShort 18 83 7 9 6 1 g235H7
  | 8 => lookupShort 15 151 5 9 6 1 g235H8
  | 9 => lookupShort 3 41 2 7 4 1 g235H9
  | _ => fun _ => none
def g235 : Forest := ⟨235,9,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P4_0 : block g235 4 0 7=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B4 : block g235 4 0 7=true := g235P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_0 : block g235 5 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_2 : block g235 5 2 43=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B5 : block g235 5 0 45=true := (@block_merge g235 5 0 2 43 g235P5_0 g235P5_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_0 : block g235 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_1 : block g235 6 1 19=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_20 : block g235 6 20 43=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B6 : block g235 6 0 63=true := (@block_merge g235 6 0 1 62 g235P6_0 (@block_merge g235 6 1 19 43 g235P6_1 g235P6_20))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : block g235 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_7 : block g235 7 7 27=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_34 : block g235 7 34 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : block g235 7 0 40=true := (@block_merge g235 7 0 7 33 g235P7_0 (@block_merge g235 7 7 27 6 g235P7_7 g235P7_34))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_0 : block g235 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_1 : block g235 8 1 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B8 : block g235 8 0 10=true := (@block_merge g235 8 0 1 9 g235P8_0 g235P8_1)
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
  · exact g235B4
  · exact g235B5
  · exact g235B6
  · exact g235B7
  · exact g235B8
  · exact g235B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 10 := lower_forest (g:=g235) (i:=0) (hints:=83) (before_sound K187 V187) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K187 10 [(235,[]),(243,[16,67,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V187 low235 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3f80007f80007,0xf807f8041181934687b9])),(BitVec.ofNat 152 (word80 [0x850a14282828282828,0x28282804100091028388]))),((BitVec.ofNat 152 (word80 [0x1fc0007f80007f8,0x7f800009e020d89f9fc])),(BitVec.ofNat 152 (word80 [0x83060c181818181818,0x1818180094000581a8e8]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe0000000007f800,0x7fa08e01c6e311e3b])),(BitVec.ofNat 152 (word80 [0x2a54a9515151515151,0x51515208800c6e111c31]))),((BitVec.ofNat 152 (word80 [0x7f000007f800000000,0x7f8004f0060703e1fc6])),(BitVec.ofNat 152 (word80 [0x1c3870e0e0e0e0e0e0,0xe0e0e04c0020303e1704]))),((BitVec.ofNat 152 (word80 [0x80000000000007ffff,0xf8000470007f803fe003])),(BitVec.ofNat 152 (word80 [0x50a142828282828282,0x828284400073002c4002]))),((BitVec.ofNat 152 (word80 [0x7fffff80000,0x780007fffc00004])),(BitVec.ofNat 152 (word80 [0x60c183030303030303,0x3030600005b4a000000]))),((BitVec.ofNat 152 (word80 [0xfffffff80000000000,0x7ffff8000000000])),(BitVec.ofNat 152 (word80 [0x40404040404,0x4040122490000000000]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(1,0,250,0,10),(2,0,249,0,10),(8,0,243,0,10),(16,0,235,0,10),(32,0,219,0,10),(64,0,187,0,10),(128,0,123,0,9),(3,0,248,0,8),(9,0,242,0,8),(18,0,233,0,8),(33,0,218,0,8),(66,0,185,0,8),(80,0,171,0,8),(96,0,155,0,8),(0,8,82,161,7),(0,16,41,194,7),(10,0,241,0,7),(17,0,234,0,7),(34,0,217,0,7),(41,0,210,0,7),(48,0,203,0,7),(65,0,186,0,7),(72,0,179,0,7),(82,0,169,0,7),(129,0,122,0,7),(130,0,121,0,7),(160,0,91,0,7),(192,0,59,0,7),(1,8,82,160,6),(2,16,41,192,6),(24,0,227,0,6),(32,8,82,129,6),(64,16,41,130,6),(128,8,82,33,6),(128,16,41,66,6),(136,0,115,0,6),(144,0,107,0,6),(11,0,240,0,5),(19,0,232,0,5),(25,0,226,0,5),(26,0,225,0,5),(35,0,216,0,5),(49,0,202,0,5),(50,0,201,0,5),(56,0,195,0,5),(67,0,184,0,5),(73,0,178,0,5),(81,0,170,0,5),(88,0,163,0,5),(97,0,154,0,5),(98,0,153,0,5),(129,8,82,32,5),(130,16,41,64,5),(137,0,114,0,5),(146,0,105,0,5),(160,8,82,1,5),(168,0,83,0,5),(192,16,41,2,5),(208,0,43,0,5),(43,0,208,0,4),(57,0,194,0,4),(58,0,193,0,4),(89,0,162,0,4),(138,0,113,0,4),(145,0,106,0,4),(161,0,82,0,4),(161,8,82,0,4),(162,0,89,0,4),(176,0,75,0,4),(193,0,58,0,4),(194,0,41,0,4),(194,16,41,0,4),(200,0,51,0,4)]
def g251A : List (List Nat) := [[],[16,67,101],[80,97],[96,81,67]]
def g251D6 := limbs80 #[#[0x21b0c699765515150110,0x3a03618d32ecaa282a82,0x6d01c2c8b80374274071]]
set_option maxRecDepth 16000 in
def g251D7 := limbs80 #[#[0x58d614c110591414c110,0x59151501105515150110,0x55161501105d95450110,0x59561501105916150110,0xd956150110d8d6150110,0xe5564501106156450110,0x65365501106156550110,0x59141541105514154110,0x55161541105d95454110,0xd9161541105956154110,0xe516554110e116154110,0x59784541106576454110,0xe454358110e453258110,0x59154581105955258110,0x59161581105955458110,0x5d164581105c96258110,0xe5165581105d56558110,0x5d76258110d957458110,0x58961545205d76458110,0x58931581205853158120,0x58951581205855158120,0x5d565581205d56258120,0x60541581305898158120,0x59772581305916358130,0xdd163585305977458130,0x5977458d306477258530,0x585515814059563dc930,0x6456458140e456358140,0xe458358140e4d8158140,0xe4984581505854158150,0x59771581505937158150,0xd8b71581506537158150],#[0x6477258150d937158150,0x59781581505937358150,0xacb9cb3ab35b2eb1ea9e,0xad35d2ed1ed17bb4baeb,0xdbadb8daedacda6d9ad3,0xcceb4eace9ce2ee1ee17,0xcf9cf9af99f8cf4cf2ce,0x59e100b6bb00fb8fb2fa,0xd81b4c30271760447480,0xcd30575650a334821b5,0x2095d850e374a1986143,0x2d7616b2ec28b65820cd,0x61ce2ec38b5d86aabb0c,0xeac845b5d87b5c30e698,0x8497594a0ad29315a622,0x55d8b94bb162996202f4,0x4f24b1186d743a52ec55,0xb219299546274a78de5,0x9f2f953e532e70b65cda,0x97542134888a655205d2,0x5e0f42ac4e85503d2202,0x2c6c8a65581fca2e2995,0xfc96559a8c2b40da1626,0x595f02d2c02d94780b4a,0x114b2c103a4860f48f4a,0xb12681a13472caecb652,0x98165511ac4a2258d3c6,0x645af2ca953e4d63eb2a,0x28ac8d91591c42b23585,0xc8e87e95b8fd1b745647,0x1120e00a806e03e0010a,0x6222c1fe1ce1a6180146],#[0x3c839435631c2e229c2,0x50c4ca4a24804484223f,0xb066e6405fe5be578542,0xa81e7d279475471e6e66,0x9d699c96c9308f08a486,0x8eb58b1aacea92a4ca1a,0xad10cc8c96c50c1ebceb,0xeaee82e40df8dced86d4,0xeefd2fa6f70f2ef02ed8,0x30fb0c30a9071053026f,0x42b22e00f82742603003,0x1c13405203580f026a1c,0xc13605a83042702e61e2,0x43140e062a2fa2f11b21,0x2ec2782fb0261c62e82a,0x6f0970882e02502b62e2,0x51e06921fb08a1e00c82,0x6490ce2f42e03601a80e,0x9c0140130ab0243642e0,0x4408608a08222401404,0x2207253770a50cf0a328,0xbe00040337c2603ba260,0xf06838814e0b03002a61,0x11405c0404330712cc0e,0x9703303706c0941d6000,0x4cf90635e7f448bc0a30,0x79d15065fa88c9dce986,0x24ce8c4be30845bfe009,0xbd4224e4c4413b844349,0x1157c458f232f8c21146,0xafb71046dc08f228f87a,0x18add59072ab056fe012],#[0x172ad0c6e853fa008b5f,0xbf2ad1033d0324c6fc61,0x665cfe200651e2177c8d,0x95db6e865acf2499c873,0xcc0ca45eeb01649fee48,0x3b51d3a7b13277590332,0x820592607aced47981eb,0x9dd640ccb9f940093367,0x5cf69a2ee8e2247aaf0c,0x29132cfb4113bf08c265,0xbe6308266a71552113f9,0x98b841b3e68803712e12,0xb87d0440e90f40c66002,0x2b60cb87d044af6e744c,0x46a7d0e611b42cec91f5,0xdf9a16cb3aa4319e23d2,0x6d1828b3a880002bf081,0x62c46d184034e885dd04,0x29783a6040f3a2278f50,0xc28c18f07c6868b1a246,0x10ede0d5e3820f2]]
def g251H7 (j : Nat) := if j=0 then 0x8 else 0
set_option maxRecDepth 16000 in
def g251D8 := limbs80 #[#[0x4c11050530441214c110,0x441644c11058d3044161,0x58932443844c11061930,0x4c910e0132441864c910,0x44154501105454044387,0x59140441635011058540,0x501105d9404416550110,0x44363501106194044185,0x549504414154110d9540,0x54110585504415454110,0x44165541105915044162,0xa195044186541105d950,0x54110d91504436254110,0x4416254910e195044384,0xe0152441865491059552,0x5811061d544417655110,0x441525811050d6044132,0x58960441615811055160,0x58110591604416358110,0x44173581105c96044165,0x6096044175581105d160,0x58110611604418358110,0x4436458110d896044185,0xe11604438358110d9560,0x5891058d624438558110,0x443805891061d6244172,0xe1d624438558910e0d62,0x591105d9644417459110,0x44187591106056444180,0xe15724438559110e0d64,0x5d110a1974441865d110,0x441825d910e197444385],#[0xe1176443825d91061176,0xd89106036244175d8910,0x44187d891060f6244181,0x6076444180d91105d764,0xd91106176444183d9110,0x48161545205893148187,0x58d52481865452058951,0x581205d9524816554920,0x48152581205456048131,0x58960481615812054d60,0x581205d5604816558120,0x4815258520d956048181,0x61d61481655852058961,0x59520595634817558920,0x483815d52061d6548175,0x60361483855d920e0576,0x50530585414c180d8d20,0x4c13254130a1d414c176,0x595504c1635413054950,0x581304c9604c12158130,0x4c1525813050d604c141,0x591604c1635813058960,0x58130611604c18158130,0x4c37258130dc5604c365,0x58d614c38158130dd160,0x58530dd1614c37258530,0x4c37458d30591634c383,0x5d9644c38458d30e0963,0x5d930a1d644c18759130,0x4c1839d930e11764c382,0x603614c163d853061e76,0xd853061f614c183d8530],#[0x4c187d953060f654c374,0x58f724c186dc53058f71,0xdd130607724c165dc930,0x4c365dd13061b744c165,0x1d9624c9761d93261b75,0x5454061b704c962dc132,0x50161581405456050176,0x59560501645814058d60,0x5814060d605018158140,0x5038158140d956050185,0x61d61501765854058d61,0x58540d95615036358540,0x5017658d40e156150383,0xe0576501835d94060576,0xd8d4061f61503825d940,0x541864c9505893254187,0x9d9415417650550e1d32,0x58150dd9415428750550,0x54161581505056054132,0x59160541635815058960,0x581505c9605417158150,0x54183581506096054181,0xd9160543625815061160,0x58150dc9605437158150,0x5438158150dd16054373,0x61d615417658550e0d60,0x58550d91615428758550,0x5437658550dd16154372,0xe1d615438458550e0961,0x58950e05625418758950,0x542765c550e1d6254383,0xe0576541825d95060576],#[0xd855061e76543825d950,0x54374d855061f6154180,0xd8b7154186dc55061f62,0x58960e0532581624c960,0x5838058d60e016258163,0x589715818159160e0563,0x5c56059571581645c560,0x581645cd60e0d7158174,0xe0573581745cd6059573,0xdc56059771583825d160,0x58181dc9606177158183,0x6177458181dd16061772,0xdd56060f7558181dd560,0x58985dc1626077058984,0xe0572d8185dc56260f71,0x7e3fc7b8df0ff855cb60,0xbbd6fabf4fe7f4fd9ef3,0xdafb5d67ecf57eafb5ee,0x6bdd77adfdbeb776eadb,0xdf97f1fdfebfb7f2fd5f,0xabb4fe9ecfd9f73de77c,0xb776e7dbdaff5f6bbd5f,0x7f2ee3fc7b7f6fcdf5bd,0x76eddd7b9ff3ee75cdf9,0xf3be73cdf9af2ddfbbe7,0xbed3d97aef5beb3d379e,0x4be67bef79eefdd7b6f6,0xf67e4fbdf77ee7dbfb5f,0x7f9ff1fdbfa7f3fe1fbb,0x5694300dd4c801ff3fd,0x7c85901b4d5405cc58c,0x83911650cd35502cd976],#[0x519365d062e57217b45d,0x94d80b922601e5086d17,0x7537b95ccde519636425,0x648e6d1753814e54dee5,0x17643c15950d51524214,0x65d11f1d6445cb58912d,0x459461a8591880b92503,0x34595d00b926902e49a2,0xad165748f655cc996576,0xb82e4a443d9573a6595d,0x185620000e616c51905,0xb2e1800c986003f5d8,0x802fd7600db590037d63,0x6009c65802cb8600b261,0x4806cb84015159004739,0x76021ae5006c384019ae,0xe500a1d9603255d80ce9,0x98605bf5d8176d640587,0xb5501b476306d158c1ac,0x476506d15941b6d6406d,0x326181a739506b26141b,0x865940a1c64428739107,0x63d5d8181d980a0e65c2,0x1ebd8507db6441ebd860,0x82d61420f5760799e54,0x2a71910a8766020e976,0x80a8e65c2ae9760a9965,0x50221f9609255d8241d9,0x640b07e5426c79209bde,0xe182cc9860b3f5d82d6d,0xd540c9ce48335d520cb2,0x2e103347640cd1590335],#[0xc9860cd75943273940cb,0xbc5d82f55620bb2e1832,0xe61960bade182eb5860b,0x1c644401f980d18e582,0x301d98100e65c4061951,0xdade1830b5860c3c5d8,0x8426195109c64442e976,0x5110766042399710ba5d,0x44381d9611255d844b56,0x760e18e503863920e576,0xe443c73910f3ce543af1,0x1950f9c6443e1f940f32,0x7650461d980f8e65c3e6,0xfd7417515905d4562170,0x4f588593d62151ce4454,0xee973179665859196516,0xdba5d4765b9517ba5d45,0x563b9519ba5946659951,0x1a1ce44612964159ce44,0x7c73911c0ee5068e964,0x616c65945b2964168765,0x4462f574188e65c5a599,0x751e16e5462e97518d16,0xd946ae9651a9665478e9,0xd951f9be48723b951aba,0x6e48654591193c5d4641,0x59941e966487a5b94191,0x876508073911d0ee506c,0xe1d9604b058c12c56204,0x503e5c101f900423e1c0,0x4eb56513b15884e0d960,0x128ce5c486f901207658],#[0x4880f971307e404cd576,0x52123e14849576220765,0x448c0d9722866448a339,0x952383e54860d9723066,0xe44b691752d255d4b20d,0xf952e03660b081852c06,0x3660507d8614036589e0,0xc9812503e58520f98140,0x365c9a199126876409a,0xc1d90270ae5490878524,0x48365c9c7d7627066449,0x9897902637e50922b942,0x2f03e549887942623e48,0x4ba1b9130245d4be9575,0x5311f5d8c20d982ea061,0x48a03b902803658a40f9,0x91288e640a22b94280ce,0x654a60d98288a650a235,0xd952b0ae50a83b902a03,0x3654ae33922a8ee40aa0,0x196535cf588d73d62350,0xcf58cdf3d62394f588dd,0xf3d8337cf54cdf3d6537,0x8cf648e1196536cf614d,0xe817933345594c83b913,0x3f8ae50eed5753b43594,0x4f0339134c3594cead65,0x13d2b59500d5753c8ce4,0x54fa0d963e03e44f6279,0x7642d55890a0d913f036,0xe510c6b92432d6190af1,0x96249ca591153d62441a],#[0x5dd12cad644b3a59126e,0x59964646595193d62462,0x16e551aeb7546ce58d1a,0xc39954a3a5952839914a,0x79ae511cfb74474e5911,0x2a5b9547badd51f39934,0x4abad952ae9654a8e645,0x1245992491be49223995,0x84149591033563409665,0x8d3035914c0d645060f9,0x944bb8dd12e0d984c385,0x6613235914c85651344f,0x3745325dd14ead645383,0x5e51508b745413e514ce,0x2f945683e51520d98550,0xb85955e89635883e515c,0x7d86582061560898557,0xe2ee113615954e836616,0x38e3654e38595382d914,0x508ae513e15954f0b655,0x1647d865920615642196,0x65a0b64d6839905a0366,0x55660f915983661687d8,0x945a83e515817945583e,0x645460d955103645440f,0xf945285e51480d955183,0xa5917919655dca591760,0xad656219e51812964604,0x19e5183296460ca5917a,0x46794614a6517f29915f,0x507641944994640ce497,0x961d906592651920d976],#[0x660ce498e3392630365d,0x19a8f82668ee419a3392,0x1682360da00d95678ae5,0x91b63b90672364da08d9,0x657046595b919656dca5,0x591d0eb62743a589d119,0x165740e651d0eb64743a,0xb591d863957146595c4f,0x19656d4f589b49774762,0xbadcdbb3d726ec6595bb,0x51965718e645d3196570,0x246595c83994753a591d,0xd719956fca5d1be63957,0x6b46595ca6f92728e645,0x1b035916c03661b20f98,0x7a83661e43591790366,0x45e64195788365dea1d9,0x977b07641ec0d98798d6,0xe4dde35917a0de45dc0d,0xd907b88659e013957785,0x6160897748104655ee1,0x39907e03e52060d98822,0x896560e39908389655f8,0x88f876983e520c0d9883,0xc84655f20d966a83e5da,0xf00d977d04655f40d977,0x8283645f61d907d87e41,0x1fe27957e8be4dfa0f91,0x18083646003b907f0365,0x162233928929e12200f9,0x948d88e52320f948d27e,0xe5610ab85842a58a120f],#[0xf958e16e4214ad658595,0x765218ad648603e463a0,0x9f858a8ce4a2ca7848a0,0x235d630a9658c16e421c,0x20f949003e463e0f958f,0xc03646500d959383e524,0x460f955c83e457233955,0x9283e424a0f919203e56,0xc1a0f949303e424c0f94,0x506e45941b919306e458,0x182d91860b6464421919,0x640ce46483391620ce4a,0x5943565860be46503391,0xb920f646443765860c59,0xe6503e79920f9ee503c7,0x496517d258c5f9154171,0xc05cc6f498517d260c5f,0xb49641c406106949651b,0x6d95945b718416dc5905,0x4b49651cd26146365851,0x20b359489619112d9640,0x8d59161351de5496ed76,0x235e4584d78163356358,0x94dd49633759594d78d6,0x6331d2644e07b9339525,0x594cb61653262588c979,0x9913450594eb41633ad6,0x25912149624864605155,0x4985479ee5120cd84485,0xdc5917791615dd259523,0x149655e5258d7965655d,0xed25957a7b915e9ee4d8],#[0x7f49915f9ee45827b955,0x629ee4d847b91615264d,0x5b771646de4585b67791,0x46f52591b949626e5959,0x41af49936fd2645bf496,0x6489ace0e1e75916b9e6,0xe4e1cb1648bac5921ab1,0x23002200005f958717,0x4803f806900a90110019,0x1df037806600b5814a02,0x413d82580480087c0ff8,0x9a0cb018602ea05940a8,0x3e407880e8c1c1836306,0xc256848208ae10c82068,0xe4154c299051009ea133,0x61e0bf4173c2dc05950a,0x36206a00cf619903208,0x21d8c3a087200e161ba,0x82c10161f983e087aa0f,0x845b889710ee215841f0,0xe25b04a309261216236,0xa1e140e27bc4e709b113,0x85668aae150e298851e8,0x462e085ac0b40163a2b9,0xc4718342fc45ed0bbb17,0xc6750ccb194c320c6370,0x72364c6ba8d531a5c340,0xe601c6438506fd0dd41b,0x7888ef11db43ae47498,0xaa3ee47ca0f691e923ca,0x8220ba40c08038fec1f,0x488910fb21b8430084d9],#[0xb246e88ca116b228c44b,0x28324cc491491611f923,0x899d930f25dc4b509579,0x1a4fd09e993b427164d8,0x4c4293051d8a2b142628,0x4ab5153c2a385404a6f9,0x9e58b8b0515eb2b7c565,0x7162db85af4b4816632c,0x8be797ad2f245db4ba09,0x4c61e8c29983330185fa,0x9543264645cc7e18d131,0x8cf819da335a6630cb79,0x2a69e0d2d9a493448683,0xb3436186bd8d669aab35,0xdfd1bd8375c6e28daf1,0x4271dce2b1c393850703,0xd513a68743ce751cc439,0xcf051dd23b547650eb99,0xda7b40f589e823cac787,0xfa73f127d68f9c9f0f3d,0x902b203e402c7ff4fea1,0x76843507420c3412c81f,0x1eb439486990c3a15d42,0xd13a225744748899101a,0x9c8cc1184a2e8458a8a3,0x41d47e68f251d1237746,0x926ca4b4491c91992202,0x7896712b9a5504a5a941,0x67f4ca098b1306a5e44b,0xd39aa7114dea9b45350a,0x109fa93e627a44efe9d5,0x8a4511aa1a9428a83250],#[0xd4a029315216a38d4642,0x8a7714dd29995308a57,0xab45532a9cd5222a1f54,0xd5a92b375626abe156b2,0x68b0495f2abc05734add,0xcde5978b26d63b2c5358,0xd6bd2d5d5a76b47167ea,0xaab8bd704ade75b7eb66,0xeed5d9abad174c2e725c,0x57c82f715e84bc95783a,0x72c0617fd2fe25f82bec,0xdf6198c29d841305f60,0x98c9316e6284c4a1880b,0x9ac8c590831ef63acc6d,0x2e26574ca8d946326d64,0x59d4338866c6ccc1985b,0xf8d155a13b40c67eecf4,0x5376a24d3d5a60b49668,0x5ae635b26b26d5c1aab3,0x58da19b3436436c38d7d,0x74c6e4cdc0db6fb6c46d,0x1c0637e16f66de31bba3,0xe8e319c4b387370a6e0c,0x98d72d8e555ca0b91f71,0x5d1eba1c73ece735cd93,0x16eba5d5cbaa07502e97,0xbe67774ee45dba3b4476,0x1e593c9778bcf0f1e083,0xfaf559e993d1679dcf34,0xe247bdef74deddbd967a,0xdf5e3e997cfaf971f22b,0x12fd9dfa23f287e0cfb7],#[0x318026ffc1fe0bfa97f,0xa06940b4812d01ba0274,0x7106360a54134822103d,0x28784bd08ce10841ec83,0x61a0c31f85fd0b6e1594,0x230fbe1e643ae870f0d9,0x4c4892f11ce22b443488,0xa2c845668a6d141a271c,0xa51902312c60a8bbf16e,0x6ca8d611a4e33b46648c,0x63b4474f8e591c223724,0x1f1fe23f1c7cc8f511e1,0x8ad912321aa428482e90,0xa4a24929920f23b24694,0x4528064ec49af92fb256,0xadf95752a32531ca4794,0xa5bdcb6596832c925804,0x9530ce60d4bee97a32e8,0xcf699a532aa649cc7498,0x66c74d699a8b349e689c,0x9d38a6703cdea9b9936b,0xef79da13ad27474e639c,0x67cdcf7a9ead3cde78ec,0x67407a8004ff19fab3ee,0xc7a1634242838d054a0,0x68acd145a23f43fe8705,0xd347468dc51a0a31745d,0x270a4bb48de90dd1ffa3,0xa2e0d3098184260ce09d,0x301f0bb1701e45e0b821,0x600c81540fe0c0380e07,0xbe0713404c01a158308],#[0xd8590c1140170104426d,0x923226689842e016041a,0x6e158981b0344381682,0xe0b4258430c0760a90f7,0xf4282311e09020011039,0x3411b061041001722610,0x31f0b25c896817028194,0xb0409b82197f088448a8,0xfe0424006b2e04b82897,0x823c8d07dc5f0003a05,0x838a3a1486c4330111ce,0xa9707f41d41697308028,0x260182b41b84223c0e81,0x14a35cba81a006070118,0x266036198320358381e8,0x28090906c46c2320e125,0x10251042885201f11a02,0x1d00b0a50c8160646374,0x24185582844c220bb899,0x682a41400216c6d0e11a,0x7c4218520d03904702b1,0x911843a6504b01004f0,0xe0e42d0d612d08a0d049,0xd61a0f01d99b53743d87,0x380108e61bc31a1a8a90,0x80805c082204d98aa1a8,0x45f0890a224c4d89206,0x2c812018144660460680,0x10c8acb85150bc5e1c93,0xc79122323fccc24257fc,0x84b14b50d9ffd124066d,0x1e6bc323878d1430ccaf],#[0x7f160464d9c9e874508b,0x122e5902524f316a0a3d,0xb002115ed0021218bcba,0x2145fa1d1424c7922338,0x909d1f8270266e7e15d0,0x8f2442717d164cb8e580,0x3591663a4337d4644272,0x35339f5945f482a107e6,0x856fa6138233138bd542,0x219a9d6627d0b4eb313e,0x462ffeb0044ccdff9149,0x6625a7932002177c7360,0xd06fb3d09be39b0231e6,0xc265e7c90af0804d85e8,0xffc6c00216e6812f7ed8,0x50d7fd00ca1ffd800ca2,0xe120196e6212a7ed84a6,0x43fa4032b7fc24032b7f,0x22232992491bff24032a,0x54fd111933fea0265afc,0xc8066a7884a6ff710848,0xdb1119413ed900ccdf4a,0xbfd8c8cb6f8a4b3a21b7,0x1210bf1a219531da2197,0x1919e6fd035090e6fe66,0xe98d88cc5f8d10cb1da2,0x4960d092ea1a3b443277,0x6bd110bc8310ca9e1886,0x594085cfe808c97f1491,0xdf46019adec22590baf2,0x80d02798443716ad099f,0x2b7fc5c465cff6fe882a],#[0x310ca1e6cd5ca33dbe29,0xa49beba19146fd110bc8,0x9b40cf89dab50467bf8,0x738861e7a87419b3f9c,0x21225ea806cd0655a8a9,0x94ba3819edcc84a4f644,0xefd240994bfcb1c0cbdf,0x464d7b72a12173a8a465,0xc91588b597e45233478a,0x464b98d15a4d19d45232,0x793c60a143fe132c4113,0xe4045bce0481c83c2655,0x650e9e0032ce4044dfc,0xbc23531139020866fec0,0x2268e044033b8455fe80,0xc2033e7f3a1781987c70,0x3c84bdffc9e0656fdbe4,0x2281a7c22aff405e11ad,0x441f1c089a381127f470,0x686e11e39d29a0cc3678,0xe3d48ca0f82c11428feb,0x8cc24582269cc93a465c,0xe4c81dc1536551ed2207,0x50c9990feb682f123b84,0x18be8244ca06bd22416a,0xe1e7a85519bdf474ca0a,0xb7eb388119cbfb9c804c,0xc5222787801947975e22,0xff34570010ca78a4453,0xc2407f2520cb9eb340cb,0x6661187bcc222f03e34c,0x432fd7a422adf60455cc],#[0x67ff032010a6fc52cc40,0xafe681950dda64d90a67,0xcb9ff6808cbb8e7d114d,0x8006e32183f18933c2d4,0x9fec26b7f12ad00436bf,0x16cf9fdadf039b3834c1,0x47cfed888b0674f8b060,0x1998461a7308a87c6998,0x3365fd5308cb7d811573,0x81614abbd01963b65248,0x5cce3ee9703c090efe50,0x2297edc8832660f1c94a,0x97ca808ca877d116557a,0xf212b2e07c11906f8222,0x20f348733fcb81c4480e,0xbea0005253e0481d3803,0xb39c45187f90992f2236,0x19006747e90021079a43,0xdbf63790428f348659ea,0xf163e0050c0fe2cc4142,0x3e3df0010d1ff2b50ca6,0x7de03253846097e00421,0x5f4a11081d72864a191b,0xaf5e64146d7829a5221b,0x16dd6cd010a2ecf4a442,0xc88654c3c4324bf92422,0x10b9e43193e912213bbf,0xe6b3f04d391106ff4d29,0x9f00bca80425a8d6648a,0xe6e82d50d217cae86690,0x654e1c43227db6464f55,0x8458be07140297a9db28],#[0x864e7653087090ea49ff,0xd433fbf151c1221b3c38,0xe009090adc74636ae12a,0xc776c335454ad1e8c6cf,0xa02144a8cae86692d1e8,0x60e56797f248442dbad9,0x61c66eeff221963e099,0xf21fb68d3eba1915bf98,0xa8a903f518f668c668cb,0xe191316e8c90c904e666,0x3589a522222dda322625,0x7ec11422cf463346c7d5,0xa395e6a2c3b3b48585f,0xf0ecdb2f0a1b1f05b213,0x832965f04665359fc268,0x357fd548650ca597c119,0xcc1e001e04cd1e01bc23,0x86eeb95e03376118f80,0x65ec229e00cce078b2c8,0x6119abfeaa432f61df00,0xd38742efbfd02287fc69,0xa2ae84ea8d4aaa52c3dd,0x2ae9e315367a618f32f3,0xf259c2886a78331a1000,0x5eb7c064a7f6d8084053,0x3a169e0cc6842f14ebe6,0xa44297bed5399a5fccdc,0x9aea28a36ba8a2dbfe34,0x56ff800c8f7e90181528,0x9dd9246fd3404ca76702,0x5919c4f0b22a7f09c132,0x213042fee41119b8beee],#[0xb8122df9080a929fc624,0x3347c2c00ca11f9a0653,0x9901957e4c22165e6948,0x901979fe5765404317fd,0x1f090232ec684454ffd9,0x2419768c422abf810909,0xbff4480cb23261153ff2,0x2877dbc80cdd972a4194,0xbee1d266d986effa7203,0x22137df8222837e808c,0x61a45953f5e888cacfd7,0x65c7645d0944ec1c5237,0xbb22a131da874245bd1e,0x99598e0e1091ef4a6457,0x59943c661a459ab943ce,0xd2c214dfd5606856fa58,0xbf4e8a10a952e164578a,0x7c5346f6dc41d7b20b22,0x486451f255179c8a83c8,0x24864f7f26b1a110cdf2,0x48842f0347c4444227f,0xd32b7dc34c8d4e4c6cf8,0x9b1d94123c6c76662879,0x183d72158a1c072cc01e,0xd12858716aa21072219a,0xdd861d8cf5f9431e3572,0x9dbe110ca9fbe808ca5e,0x1b3597be50c6efd89108,0x46af641646ec366b2b76,0xe3b731a8f08745c87c53,0x1368f01d06d54cf1db98,0x83eb4724e124e1447a8f],#[0xc32034d30121483fce58,0x6ea66ee2a138233d7fc1,0x11239e03418e710f3d34,0x41849b226f661ce3433f,0x8d4682ec103f00ce0872,0x27d0a1c5b464efcf8790,0x2e2c970788912e129d66,0xc970788912e11a1e17eb,0xa964eb850f292184b3e2,0xb9a43ba179b41da2c283,0x3185e0051b49dfa9a326,0x7ce44d1690a354b2127a,0x42f37412dd0bd817f019,0x2d20330d3ca26bfee8e2,0x5e267cfd5596889a0bb7,0xa0232a73bcb23317310e,0xdd7d0119683e59195baf,0xbca4cccecffe85f0090c,0xb15943f5bb51133e61e,0x9281420df4440fc624f0,0x66ae200c9ad3b8008587,0x4217582520cd115c3d33,0x9000a4c8f6406545be00,0x268df82226e39f445fb8,0x2201bc305658e649f8a2,0x7fbb45b3ebfd23808827,0xe5ea6d985c0fa03247a5,0x870612cfaff7226790c4,0x83d8c2353dbc184b3a79,0xf9939fc4e28e8229138f,0xbc1c78b26dd79a8acd8,0xf630b40d8ec82f820b71],#[0xe38839cc68c668e6e40,0x51d91b11d8f1b209310b,0xc0c2025fcd4620b61c0b,0xa396cf1c4244716354de,0xd363b2d7bd616650a683,0x3c86a90b14efdaa59b8b,0x59941ff9174217bc7325,0x7d5b883ab6123656e748,0x19fe800425b960741148,0x4a110967388a3eff9099,0x774f10c99f836b50ccef,0xc9076561f090bdeb9432,0x7155e43187cfad432ca2,0xcb528503b063d50b2c05,0x42843e0c1c184b4b3f77,0x65a97bfdaa732cb4d5e1,0x8a181d3c0df30af7c080,0x596967307670bc7785b2,0xd5217ef1959491f2e42,0x1fe000844e3f20465a79,0x4257be00c86e0f800215,0x5a8656e632a19b9e3e01,0x1cf02747cf1e734207c3,0x4bc7482b8a188e401c69,0x554c9e102d196506be42,0xa7ce22a0854c0218399b,0xe61c184b3cec56286690,0xf8e4c4521ba989352cc5,0x778119b4e883369d1066,0x589177cac48a73119cc4,0xaa42e22f30788bcc1cd7,0x213c2034bbaa42834bb],#[0x29a4b1cd4d18a9ef089e,0x8a55b1c133394d275967,0x491b820b0d2e15151ba8,0xed1450b4669c1bdd525d,0x6c77b7c685a28c2a335d,0x793a9a129d3ec1d95a70,0xf360d08e7f5153a7d832,0xa00a97debd0db0228737,0xd6284f66cbb7142f1d48,0x45c98a0cecaea9b480b3,0xc1c4ae2343746098b369,0x2bb5cc6e105e86b4d0a2,0x7c685e2e4db24377ad34,0xc0f8a428a179bb82f6eb,0x4a657e2837af4d17d514,0x73a8925c6c603133e305,0xbed0e6d1a5a1f366b4b4,0xd1d498c3e6dd70b473a8,0xd68cbf9880a39d46571b,0x281e7a4eba014ea4e86e,0xd1d8a98ec393834f46b6,0x4bf8ba100b39d46045fb,0x80a9466a86f48e1c9a40,0xddc1ab5fa08d0a5732af,0xe348729052ee260c2f35,0x97497926070f9f3b8353,0xb971a8cda1b570806478,0x1f5a1060278367566830,0xfa1675e121af04c21fad,0x8fdc2596bfba3cb412d1,0xd40e1bad2e0c0cda2f42,0xe451453617dc36ae1364],#[0xe0a0dca26756683ef262,0x905c249d3610dfdd13b2,0x8dd2a8e69df28fefca2c,0x41452767624be0592a93,0x24fb]]
def g251H8 := limbs80 #[#[0x6a042e2ac1e4028a,0xe59aa1c348800b70cb11,0x413ba000300368000524,0xc280010f316efc00dae0,0x6e300042e001a6e86610,0x841cc6a0000012700101,0x9d0118c11fc4c436ef6c,0x5008a817c4900081c635,0x98000063d830875dd130,0x6a6434ae480026162952,0xdb8c1c8722f49a1104c6,0x84ac710b35609e001a1c,0x300120b4d747f578911c,0x6653381e32224a7e10cc,0xa151f610e90001dc02d4,0x8118154760672114e372,0x299955303ce221e92b25,0x4bc8ca205248d4630138,0xc024554b80ed550d2104,0x40f1de4a351502f0b225,0x2a13a06c8822501c0282,0x240a009d100cbe91c128,0x10e8440691d484026003,0xb936036558a186e0001b,0x9d8514c44d73d23184a2,0x320c2848a0331701fd,0x6c048e]]
set_option maxRecDepth 16000 in
def g251D9 := limbs80 #[#[0x54110501104c9104c110,0x58910581105511054910,0x5d9105d1105c91059110,0x545204c520d9110d8910,0x585205812054d2054920,0x5cd205952058d2058920,0xd8d20d85205d9205d520,0x505304c93048530d9520,0x58130549305413050d30,0x5913058d305893058530,0x5d9305d1305c93059530,0xd9130d8930d85309d930,0xdd130dc930dc530d9530,0x589321d932dd930dd530,0xdd932dc1329d9325d932,0x58d40585405814054540,0x4c950d8d40d85405d940,0x58950585505815050550,0x9d9505d9505c9505c550,0xdc950dc550d8950d8550,0x58960585604c960dd950,0x5c9605c5605916058d60,0xd89605d5605d1605cd60,0xdc960dc560d9560d9160,0x58d62dd560dd160dcd60,0xdc562dc1625cd625c562,0x5cb6058b604cb60dcd62,0xb7ebf9fe7b5cf625cf60,0xd7f3fbfefebf6fbbdeef,0xedfaee7b7fdfb7bddf6f,0xfbbdff7bdbeffbeeefba,0xff7fcfeffafdff6fcfef],#[0x5012591ea8b112ffffe,0x22504044908045658a07,0x8c03ca18079320112c20,0x1ebb00238400430801e5,0x82895104470c0086180,0x218504dac809b550144b,0x10712820c861811ebb02,0x47080d95501b2a903896,0xc0c861819ebb03656506,0x6d8832cb10689610c470,0x311c1863d730c7ae419,0x1c2063d740cb6c819659,0x863d750cb6ca19659431,0x787020b0e048e00091c2,0xe0b0e10e5c8211c0040,0xf0e1c161c39cb9072380,0x24161c60ec08c2180180,0x61c283c3090785120f06,0x682c38829761062e8201,0xc38d29761a3b02348600,0xb0786140f0a281e0c502,0x622502a4481e10583c10,0x4b6ca49659491eb99281,0xe686608d10c01a3d752,0xe5d8830b2903973200b,0xcca41c0141b8620330c4,0x82c3911b852872ea50e5,0x1b07872a0b0e54d5cca,0x3f802e0b0e6c6608d90c,0x52c0f0c5c1e14b83c097,0x3304708600e02c3962d7,0xc601e0cc03c098058738],#[0x1e0cc83c0993f80320f0,0xd0b2a9217932420f0a64,0xebb21656542f2c685e50,0xa3238642430c84fdd909,0x96246f2648c8e0519fb8,0x46f2868cfdc91adb1235,0xae88d6d911acb2237963,0x8d6d951acb2a33f74467,0xdc8eba991d2385467eea,0x68bc1a44d63482f067ce,0xc3ad15835a9ac6b48601,0x13563626a86c41609882,0x523cf700781619882c23,0xc6aec785e14f3ab11e75,0xe945e18f0ac31e37763,0x4161d70ac1ae21805c0f,0x1591ab1b20581644700a,0x1bbb203576400b0cc816,0xa2635744c2f0499ee013,0x4f654c9aca985e1131bb,0x5e0b0e9c5e1531bbaa6,0xf02a8161d78ac1af218,0xccc1615982c0b3078654,0x560d810c0302976500b0,0x1a02c13405876052ecc0,0xfc02b2380560b0cd0161,0xab0784560f04ac1e0559,0x587582b06b08601603c2,0x6a0b08d41609a82c0b50,0x2caf5b591e91c0bd0585,0x44612090c0415b657ab,0x61e110c04207877e0b0f],#[0x283c1c03b82800f03001,0xb14559628a470314fdc6,0x523838a7ee714fdca2ad,0x658a7ee9156d922acb24,0xc0b0f303616610c04c65,0xf0c161a702c24e05829,0x43616690c04d07878e0f,0x1a782c1cf05819e0b0f3,0x90c04b0782940f032816,0x15e0582a00b0340161e5,0x584bc52c978160ef02c,0x7a2aac5441616f14b2de,0x170b4d6e02991c053078,0xb7c160ef82c0df0985b6,0x160b002c0e02380a80b0,0x6e02c2e02965c00b0980,0x2c1e10581c2370564261,0xe20984ba130574161708,0x584c40b0788160b102c0,0xd26ae7a4e5cb4aab1690,0xf03ac2e17503c3e90587,0xb01e07603c2eb0783d60,0x605d03c2ec0784d80f05,0xd02c2ba35637472c4e81,0xc1b775636e3702dc1619,0x621806caeecdd51d9bbb,0x76703704e01a1db14bb3,0x23304e4ee09c03c0382b,0x3981601d82c3b92b767,0xc1603382c2e60583cc0b,0xb182c2e70584ce0b079,0x82c0e80580d0170d946e],#[0x2009162000f03b41e036,0x91650526c60a458c148b,0x20726c40e45881c9b282,0x23080e4d901c8b203918,0x41a44c83494303918607,0x450c348c10691620d22a,0x348aa0691830d22c61a,0x8c28691650d23081a459,0x125860282ec0615880c,0x17608d2ca121588213c3,0xf27001c9e18212c3044,0xf0a1d05d4393c1874173,0x3105d4612c18c41760e4,0x600420bb054165124b0a,0x420ba882783111b02224,0xc18d41871082ec209e14,0xa4183144b0a3505d4692,0x8216850c290618520c28,0x487082d06105a1c10b41,0x24a4584948a89291312,0xa460c948b19291532523,0xd8742b10e91852522ca4,0xb4b28f85621f1ac23d05,0x1138552264b0c3d05d87,0x278326bec64d758c9c2b,0x52682ea4d7d949aeb293,0xbac669061c9a0bb13278,0x6409614d2eb29a258334,0x1594a42b1948553290ac,0x4aaeb29527812a82ec46,0xbb1527852a82ea557d9,0x96258536baca6c9604da],#[0x1762c4f065a1608b13c0,0x424b06709604e20c3964,0x30c8646110c8b2219162,0x8e46051c8a0a39121472,0x5911c8c12391624722a4,0xec2b11d91854723088e4,0xb19f8d613e86ec7505d8,0xf43763e82ec7dc590fbe,0x873e830e7c9e18f92c31,0xa86e8917591221b92442,0x8b50dd16aeb22d25825,0xa1589120b2314162624b,0xd52beb1a527814a82ec8,0x21bb2541764a4f0a950d,0x2267d644cff049905959,0x43754efb069c9e053bfc,0x74e86ec9d05d9393c2a7,0x86cacd05959a143a7418,0x8ac9e09592c230258260,0x9609621c22b4382564f0,0x5ec8b0bd91517a4b08b0,0x8b2bd91837b22c6f6460,0xbe91807c82ecf24615ec,0xd657c4f06f97d8df2eb1,0x7c82ecf89e15f2fb2be5,0xb0b04960e0aeb1c14187,0x9606120bb3f27817e4,0x5862c8a0c54183808303,0x2c8994591818b22e3164,0xb1c591828b22e516458a,0x591648b23071645ce2c8,0x768882ed1246122c8ba4],#[0xd2301190a1e220c3c443,0xc9189e0a321b9468d718,0x89e12321ba465f648cba,0x1e320c3c643768c82ed1,0x12c14c27878c850f1896,0x9482587984b09310dd26,0x42769082ed2105d2420b,0x6870ac50d0d8a720b14e,0xae51c9e06392c343417,0xd1d05da393c1c743738f,0x9606693c3c725878e86e,0x6520bb4925879a4b0734,0x1c0ca4181944f05289e0,0x4b258196870529060a52,0xd62acbac949758a912c1,0xac4f075905ceb20b9565,0xacb589e12b20ba565d64,0x449e06893c2d64175acb,0x5969aeb1d32785a2bacb,0xba0b9d75d75a6bae74d7,0xb2542781a882eb5d7596,0x89380b04f0b509e12a2e,0x84b082e9617592c13c0d,0xa4f0b6105d6c2eb2d827,0x36905d6caeb2d95d81a,0xa1e05b93c25a2783b44f,0xd7213c1e44373c882c79,0x92c1e74173ce4f0b910d,0x2e74183ce82c79c96173,0x95630e4b03a09e072a0c,0x3272ac64e559444ab287,0x2b025656149cab293958],#[0xafa560df4ab1be95812d,0x5e05fcac0bf95857d2ac,0xa34ab1469676892aed12,0x7800095848d2ac91a560,0x42406f00ac0102015401,0x30a05d80ae8141024a0,0x4020403d807480de819d,0xb3c156028c04d2092411,0x7040da41a2031d05f20,0x6843208160fac1e3839f,0x37425e84a7090a119822,0xace154429a851d09ec1,0x985f20ba8170c2d1858d,0xa9c34086620c6a189030,0xe881cc438806f00d981,0x88000fba1ec83c20764,0x2f8455888a10ca211441,0x12b224d848a08fc11b62,0x989fb13b426f04ce097d,0xa545370a53148228a850,0x16602c485798acf15642,0x38baf172a2dfc5b00b4e,0x1106198c1917ea2f785e,0x19a832f06520c8418c63,0xe0d5e1a7a34786850ceb,0x7ec6f18dcb1b6636546b,0x1d02399c7278e331c2e3,0xd0f091db63b2875d0e99,0xe5c7bc8f4f1e7c3cb478,0x20343fec7f28fd41f663,0x7908720d64154822102b,0x4dc89190fe21c2431485],#[0x236e46588ba9166229a4,0x2122e242647f48f391d0,0xae094f928624ea497c92,0x26a44cf898e92f925b24,0xd13d4277c4e749c19368,0x228a391459287a50809f,0x29fc538ca6514b129405,0x9959d2b005568a9c9519,0x8c0b0f960a2bca5740ad,0x2d785aa4b44166b2ca25,0x17602e765c78b8196e2,0x5cbf697cf2f5e5e7cbc,0x31746258c3a1854306e6,0x4194f32506440c7898d4,0x860cfa99cf334a6618cb,0x358a6a9cd409a56346e6,0x51b6b36b46cd8d8b1af7,0xa0e039be9378e6ea4dc,0x39687240e3b9c64388e7,0x21d4d3a5c7430e741ccc,0x7d0eea1db23b2c75f8eb,0x3d387a04f2d9e343c227,0x41f333e207bc4f6d1ebc,0xf3cfd79f983eee7d7cfa,0x40ce811d01420113fe67,0x420f1419a82cd04e2089,0x6ad0c6216e429c84b908,0x449088b910621ed43968,0x922c245548a3113e2262,0xdf11af233d462c8bc116,0x484290011efa3bb47348,0x4a4c949589231231a445],#[0x5e92ad253c4a4c942127,0x4c6c98452f6a5bd4b349,0xfa6c54d3299fd332a653,0xe193ab273a4e3c9c0936,0x5074a04d3f827cd4f529,0xda90351c4a2e1447a863,0x7714dda98f52d4a4f148,0x5526a9b9525aa2053fca,0xdab585660ac0956faab5,0xad6002be15784ae755b,0x59d0b3296522c7b589ab,0xc2dae5b20b58969f2d0d,0xa6d73aae4c5c3ab7d96e,0x5ec4bcf578c2eeb5d72b,0x73032602cbfb17dfaf95,0x3a9864b0a9611ac1b582,0x6312c5c58a6b1286214c,0x6b22a6430c7b58e4b1ae,0xb0d958b29664fcc9b192,0x66c8cd4999132ff65cec,0x8b3d16758ce699c43376,0x205a37b44f686ad0459f,0x69fed3b5a6db4b7693ad,0xb5936ae0d555a963511,0x909b0eb6056bcad74dae,0x6dc6db09b4eb6836cc4d,0xdb7986eecdd49b96b708,0x1a9c243826700edf85bd,0x7236e3d9c6a38aa7116e,0x3b9ac731ee5c1ca8393e,0x9c5d22ba247406e799ce,0x7604eb9dd643aae7528e],#[0x13b8876c4ed21d953b1a,0x111e12bc0777d0ef01dd,0x79b6f2f9e503c7b78a8f,0xe3d667aa0f4e9e8abcf8,0x819ef2bdc67b5cf655eb,0x7d88fa75f3b3e577c52f,0xbf4c7e62fc71f83bee8,0x49ffabfd87f50fdd9fb,0x8159021e039404380530,0x5c16b8289046a077c0d0,0x8f610dc1f983ad06ea0c,0x86490be6168429e84d70,0x343e987870e7a1bb4348,0x216237444c8871107620,0x8aed155629144f489851,0xd460a8bcf17322d74598,0xc1237446c58d31198631,0x8f3d1df23b247448e491,0xac855906b201e3ecc7bd,0x44e47848cd9157223643,0x93cf27164c8496c92732,0xb4aab950929565174a09,0xe8e5bc4b48964b2c1256,0x98cf31526194c08979f2,0xfcd1699e5334a6564c89,0x7ea6f04db69b17358a69,0x9da53a8273cce539c4b3,0x4fb49f053d5e792cef9,0x26e83f5059a07140527f,0xa26f446687dd0dda17f4,0x551d0a36d465e8bc5155,0xa7a93e5252a44f48228f],#[0xa6a34cc298352e2a57b4,0xad414a7d34f269d2537b,0x38ea5dd49ea9015172a1,0x85c13061130ce13aa1b5,0xd41dc4c970843945c34,0x3899073830831708a07,0x60f8105c8603c15a5c11,0x60597e089be102461785,0x41c4585406456181089a,0x642306e83a043e61807,0xc0c1ec00298441fa142d,0x447050691bc1c3aa1a82,0xe284100270c43605892,0x464436102a609180ba19,0xa308c08260001209506,0xc28892d90240c020bca3,0x4150d0cb012588d04200,0xb037818034488b11d01,0x104054420a43b0441046,0x4681483c2ba358d12030,0xa488221c3f2408386d16,0x3084c347916a0ccdcfb0,0x3a1a13f4e1b203353831,0x277e94e328666ebe94fb,0x27194322719432271d03,0x5022e8c0a20f031f5422,0xf018ef70c25b86126ff8,0x34bec222133f3c281973,0xc81143f2e2432ef4b50a,0xc9e6510c3e92d191d7f5,0xe852a13367a753832c25,0x84558c0a263c9292215b],#[0x8d408d9e95e480cd316b,0x9ff11008f994300cb3f5,0xc4e24582f293141e5279,0x63231ec04a87eaa4232f,0x6f2df1314782f2936f49,0x8e7b012ef9d022d57293,0xdd811087b012eaef3a90,0xeec08842e3e01929847e,0xfcb8137433d308e86476,0xa0fc190042970a88650,0x81967e84d191d5e98781,0x2136421c79510197abc2,0x63e019d9ec8021319360,0xa033578e56098672fcb3,0xd09a323a750f4197b2b8,0x588f2a203375785032cf,0xbd4fc064d90871e54406,0x9351947331113587a0c,0xed2c708a3a7c274265af,0x5811549f181197fa5122,0x888ba8888a3bce24615f,0xdf030881991ad9c445b3,0x64ef5083223f5390885,0xe2450cb59042b0cddea1,0x392315e3a116a3a88658,0xed72418c98883f193114,0x332d9c445b3888ba8888,0x212b847ee6641d7a1474,0x95711976788988c4fa80,0x8b6711229f111751112b,0xbbea00843bc2347ec810,0x761104f638458e4cf293],#[0xe70c737c2882bb1c22ec,0xa7c0c91a7c0c937c2891,0xf1408bde94c7de900c91,0x4360493ce142377a531e,0x3538261fc70218c92a70,0xbd898c90b40553826e24,0x28c5e450c91f9143269e,0x8908b752129d8117aea4,0x21d0c8c57c48876045eb,0x5fca039acddfb18c9b9c,0xbbd79317e5792dd824b,0xfe886692481e0c5aa66,0x65af2c05329b03198ca2,0x867e8c9057c4881f28e8,0x7c2417899071be124fd0,0x44538246f8482f1320e3,0x257c12459463b08831d8,0xc0424ff18a4237b26c04,0xf1320e37c24918434726,0x7924eeda0132ce2b8892,0xb13f044668fd481119a3,0x9c1a207dd792f7ea0593,0xc2229c1237c24dd83441,0x4c83a78190631d84418e,0x64726c0427b26c0424bc,0x6092f7d129923fae2a06,0x62d5335dd4902ef5e4d7,0x79512995b607ba4440f0,0x583196711888b38ae225,0xe658feb89919a6621d79,0xd4c65f26333c24b5e540,0x11929e633a113e1a01ac],#[0x408bef319d0952465ff3,0xf8c08c3fe972632385fe,0x1957fbb111477dc08aa4,0xae483e72d09d852cbf45,0x5d8f5d3cec2276c1191d,0x1763b08988bc52261512,0x906323effc8045de7521,0x4a132874fcc0ccdbc7f,0x66dff9008a3f552115bf,0x8a1d3f3033307fc56d06,0x8a9fa7e83100346fa262,0xea92462d7a5265dfe804,0xb5545cf1e88c9492391f,0x2f5387a0ca5c7c0326f8,0xd18114a1e180ca3fdc32,0x723089b210da9f80c9bf,0x308987331127df17b518,0x8795b9957ad19291ef7,0xcb139156ce2267fcc464,0xf0c22652d4bb642f7b63,0x42274d09907f8949173,0xbc48ebe96b8491c1cbc9,0x72de101960b88322f696,0x66bf02299e424135f811,0xb671107ea0bd1fc00997,0x61e897be0584ca9ef6c6,0x8b5f22864cb96f080cb,0xcbb35f8114cf21209afc,0x3d1237bb608cbddba08,0x3f684ec2e589c8ab6711,0xc084c7f0212214fd1924,0x63ea106447a2c08447a2],#[0x5810990af40cbd8cf819,0x4ed802597b19f0328bf4,0xe75134476b920ddae483,0xc0333b0258fb50991f00,0x85effa82819a3f900647,0x36460f29732cbc58902,0xb4e5d928468f40d91a3d,0x11969cbb25089f5f322c,0xfa81324768fc8b2b7e13,0x2be1445943e3ca10acd1,0xe623257c288b2b47e459,0xf011637c2413df0114bf,0x5b7981484df4b9c4515d,0x9bd2a5c40a43b7eca346,0x648ec1ecdb287dd1edb2,0x2688ed724194e469ca94,0x7b8192f7fa4700433ef0,0xc0640fcc0645f3a1908d,0xb2710108680fcc0640fc,0x770f08432e9eb18146cf,0xcda7ac6051b4f58c0a3,0x4cf234358d6482f99421,0x9b3fe50884ccded4942c,0xc4b6f43c628cffb71109,0xf9e44492273c8428d43c,0xac200d0d17dce1a2958f,0x1ef6a191f77b50c8eefc,0xb23435ce492409f39247,0xcb9cf0600664fe0084c,0x84ca9b7f83003347f8c0,0x19964f7c0fc048a6fe0,0x10881fd80196a5fbd8],#[0x7aec065b53c1a4429bf3,0xa353b7af2120bf850326,0xed6ffbe40033a07f580c,0x40858bf01983d12b180c,0xc033b797cb01973a7c06,0x6851ef686476fc27a71,0xc8474f9f0191b3f6734b,0xf720484f9f01930c797f,0x3019cbc682d4c8346cee,0xf80c810b17e03307a256,0xf80cfdfdda7bf6034674,0x9c234f1ef2e118bf2d9d,0x338f7ffde13824998fdc,0xf7cf1ef6e891df6b7301,0x844d3f1844af2b5b9919,0x4eb7e022a1cd6046d3f1,0x3e0232adeb02369f8c22,0x97467c045558d6046552,0x79207f2e4a3297c724d1,0x2cf80b442f8e49a329e1,0x8cdfc0200a4307f2e4a3,0xd57409a3457c6c4660e4,0x791ae313440313440bc8,0x88cc0626885d3e188ca1,0xf230fe52804c4688af8d,0x43c230bc8c2f230bc8c2,0xc232adf0c2373fb88821,0xbc09a207f2e4a32c1df0,0x4ce262285e46946a268d,0x85e46237fe988d3a89a2,0xb119c7589a205e461791,0x71fd31187589a247d161],#[0xe461791c7e8a0cd88d02,0x442ef00a2474a043285,0xfe442659c7f164556596,0x2659a5f889239fc8a4a5,0x85099b3ea4484cc5fe44,0xf93b866ceb910333347c,0xb5f94109963efe5a2762,0xc82fdcc0042d3ec30010,0xc021953f1da0654fc740,0x7cfe100c82f810084efd,0x65eff420196bdfbd0806,0x9b040cfe100cbcdff080,0xc88d9fc111927bf89115,0x45a2fe88c93eb911048b,0x7c1119793e088cbbcae4,0xf6b0032dbabd80414372,0xc30192fe30253ecb096b,0x4ac233fac243cc384b1f,0xa88c4859c571103f0c06,0x21779c28459c57112df,0xb8908b1fc301901f4e25,0xe250216b08e3f950326e,0xfc301933f14720cc2e5,0x2b911448bc88c5efc064,0xe492379246af282a336f,0x18ae220c57112379248d,0x7b9023218ee04666f063,0x589a034084bee047df,0xcaa1dc604855cdc08d5f,0x1b75adc111d1e1f91242,0x9a20c4d0c62686aba04d,0xa7d168189a18c4d0d718],#[0x14ba61295151a1205f84,0x266096350b89a2aae04d,0x34304a7e00bdecfbc09a,0x9c05682167a9daf08c31,0x82afce2c44cf371f0516,0xb350e3e49235450c7aa4,0x41fceb44744933fae448,0x8513287ae142656fb426,0xa6b8c924eccd71a8d1a7,0x68680ff8294ac0cd03fa,0x38762e8da19d3c3dad45,0x9f3f98e0197ab5a37c03,0xe9746f80668e3960fe01,0x26cd2ccf48e2a879d647,0xd7cf22269e4446fb223,0x35e9e4442b5bd1196791,0xc7962688ebaa7123c911,0xa686fe132eda99e3aeb1,0x46543cf2a307f284ab01,0x2b6f44645d911150e175,0xc848791adfe48cbcf911,0x92594385f446667f4192,0x57b2bda9a10cbd0573ff,0x915abd119072fef22314,0xfde01177fe601177fe08,0xc065cdbed09966b21127,0xfdbc60033a7d603267ae,0x9f6022c7bf6f1800cf1e,0xe03261e422361a8832ef,0xb4b78032eeb58c08d9f2,0x4465b0868cd234bef518,0x4697ea9183f95a08bd13],#[0xd6a12377e9f9622809a2,0x9c6045623ea1c7548dba,0xaa9bff8224a83ff38247,0x1bc1204cea0dff3091c2,0x5f0cd18a2bdf668268ce,0x84f167b1a571ef4f230a,0x3f4a4915e56a03519d33,0x9d44bcbe4ff4a4983af5,0x10bf680065af82ac325,0xc42df602397e5800cabf,0x4655bec0465f7719011,0xcbde8bad00675d56fc,0x6d8cc3fdbbec0474f2da,0x920db001c704678e9ff5,0xba8924624ee54508676b,0x879b3779056d8cdbfea6,0x466a2ca00a55dda5b802,0x348fea7b4292427c8a9b,0xf202b482ce5158f39411,0xb3fa122a958a5147069e,0xd1b6c0c4950f8d2c6e17,0xc1e238a5f0cd1a46971c,0x3aadf808cc1ede649df2,0x40ac91e102b247840ac9,0xb2c7840ac91e102b2478,0xe8d8c944725213bfa244,0x20564f72520fdc9483ef,0xc8f27d1490ef7252123c,0xcf8cde597bc34c6d2665,0x2850ceffe8b2f3c29284,0x4610d974429286972529,0xba2cc6cba214943025e8],#[0x348c2001cf762163fd12,0x5e846115427a208c31bf,0xad5a17d949fa15ac4282,0x5850a5aed264d63ca610,0x71b304b4485c6ce047f6,0x5525a1]]
set_option maxRecDepth 16000 in
def g251H9 := limbs80 #[#[0x408018660002000412,0x4000080b0842001c00,0x24011380000c1800c52,0x3000018100080005811,0x400006400050190001b,0x200c0004b0b80509801,0xa03c0000c170fc03,0x118400340b0040800c12,0x340f0041800c020341d,0x7c3c0300b00c100100b,0xc0a0640c1cc2f0100d,0x30000e0780003402,0x45b0080000c0401005,0x24060201f0340000c00,0x8690140d29c0a1341b,0x40044e2a82101032,0x10014030450043802c09,0xe407038241b04f52009,0x1e90301c01580180142c,0x6c050000512c0304000,0x1403000820101101c2e,0x2a80d14025218030180e,0x80010083f0201c03c06,0xb80d00801044050109c,0x2c100080600c1f02008,0x1b00c0304c36008a2,0x880108c001b0000ac64,0x60d83b0003300818,0x80075483201c130c298,0x60e86f12c0702c10,0x1412044c5018431595b,0x310000dc0a0500b01c33],#[0xeb4a5f6c41a34034164c,0xe850874f20e0003d2813,0x1477968458046c00006b,0xead717448c0b020f85e8,0xfc8bf1704700c2003d01,0x68c200a4373254a3b016,0x8601d08162157070d10d,0x91e3214031a981b22551,0xc88546c18e5cbb49,0xdd6b4a6de901af232000,0x45c940dbf260b0080000,0x645dc189000050542912,0x486d24a9432da1823264,0x159fc714140c4cd225,0x9a18384fccf9890b1910,0xc1f288dc0008019c7242,0xf9c6f80000000000c81,0x4a820a21a000000052f1,0xb967cbac3b400066371,0x5a283d91131f1c06800,0x28800091b78040000000,0xcac99c59d25245b78014,0x70e7333c03a411120c46,0x1d4f020000000000014b,0xf9943217871de1576d7,0x2000315100018e8116b0,0x542e194c1ccccb030d05,0x1222479a433f998000,0x31119776d1e123b44930,0x446741dc01243a41bb06,0xc710616dae63ddd12c69,0x3685c6a6552bec670262],#[0xdd1032010240c9a45e22,0x3120528dc54028042,0x3ef85d03c2cf5732923f,0xc4db900001cb81f21ac4,0x2a07d3f70aa4666146c6,0x29d0d01f3f6e343273e,0x6c115f1e3f7d65f6c48a,0xd01660df86dc14fc7d2a,0xa01414ee2af07bc911cc,0x9678a2c182219c66fe22,0xea24f03511ab84e90bc8,0x206a8348461096b190d7,0x1c831b20ec35ad43800c,0x9e31721d500025a0b45a,0x6b88208dc51380ac1f61,0x11c9c728615801607,0x12d067e136056c0f016e,0x620fc42e7152b09610f2,0xc20d92e40e4425c21c34,0x4b8090e99d12d30b6b91,0x36410f0da800962a112d,0x7c8f4111348913440e74,0x44a8145005a19884a2c8,0x7f108ec7d90ca892309e,0x5b23b47a401437cd0d70,0x423a5975c65322226b87,0x10764f3251616d624522,0x2e83adc81126fd3547e0,0x1068643f00031b5c6d01,0x86f38ac41ca0ab00014d,0x867083c3d80000003156,0x8c0ef1a3a6ac0ee8e55],#[0xb102c127d2b857f5c301,0x42f81ad804604d824,0x5ec81310182674daf6d0,0x8412c7e915663ed6421,0x9a1f9665a61601e302,0x4f22cc32244390ba955,0xbc240461a071769ec827,0x1ec82cfa23c1,0x1238673c7390b34c5068,0xfb0002c0f00038525229,0xa121822854601dbc9981,0x11e915a833f163477b98,0x16b63bc12b179c84c8ee,0x62019400018cc6322,0x4e6487d5197e8d8e6700,0x1a2128817de17c22900f,0x8bc54f07431c34dbd840,0xa7d000092b111709380,0x406202f48f209123ac00,0x2ac000000317b5645c64,0xbe448102dc5c00de63f,0xad2133790b10219401c7,0x44605561cdd1990e5564,0xb6d9154c2261969273,0xb6076cb9c07b9fe04480,0xd2ea0ad888d842080d15,0x1660d13007580df209,0x8602b747824149a2c630,0x922a867c00040da45b49,0x17504f5c7a898c26d315,0x5d896f8e7c6934a4c81a,0x1a592160c92c6380],#[0x3cc9000123848c400,0x5311fa346904143aa174,0x4f843c40c00088280004,0x5095156962860fd21666,0x10642ffc890001d1b614,0xa4414622440394309526,0x815549e34361293988d,0x4d11f0000000984800,0x5df42b817e24d7218000,0x9058f856026984d9069b,0x8262f2b11b3337694147,0x227442c0004441212c9a,0xf9213ac85838699b235c,0x4e2b70ae83cb98983419,0x58e0000d8f400087395c,0x17000064b807ec60b1ed,0x5f08fe35800052f612b2,0x4202b4b3551c8b948741,0x1dd1948105000115910f,0x5a833400056384be07fb,0xbb3201dc85871e0a14f0,0x1442c5fe449e94d00,0x50adc6c213c8df8790c9,0x7113c12ce235000258d0,0x46c844000012f1b605,0xc2d12b0ace39b503c54,0xc900015c80000000985e,0x92800c700005,0xd1060d8c094000000323,0x7c000f245256390ea2d,0xb215000214d0002469c,0xa26c0000125450f1c619],#[0x1d800a80008454860466,0x5300028448861c219309,0xc24c8231efa40e0,0x4270e8052c00081e99e,0x1cc98028e173d1730e6,0xc0000f8cfc0b04b642f4,0xc0000000407d94c00087,0x1528c8f696b8e9c73,0x3f0380021746609c0000,0x4c3de0248602239a2ce9,0x83f8a63000023,0x69c000077c000795b114,0x205ef86701d1348000c,0x810a03e0000b7ac00000,0xf3a8bc000497,0x897fe4046fc22d0580,0xb05cb0d985220b241380,0x82a2e344674000097009,0x2027c43999041509b9,0x2304741430cb00018550,0xb0e2560000080d621e54,0x2d07a324640a0000c59,0xc87f64842d54bbc34c,0x5590d0af44cadbc36cc0,0xb339614000346b00030a,0x1861513800003c4116,0x961ccb1f5445a9340000,0x8795165265f1d275,0x85695d18d1868da8787,0xee44910ccd223856c2f4,0x4000281c861e61145a41,0x4712195450651973d84c],#[0x6eadba079c4a64133d33,0xec00000c6ccc92c51f70,0x7613c2eb226837b08a02,0x24784792578088000874,0xc5ae1e200021eb41c3,0x2006702389950b744840,0xc041068661c96609635f,0x31395197017c29c000,0xc282771fcc17c94c5580,0x601b000105b8698e3c22,0x11d18e81aa86f51b8430,0xd103fc000f2e30340003,0x4012118f884003e81140,0x258a56013f18a000249,0x61000084bfc0784320b0,0x124c371e205f044a148,0x701cd13615d81b613100,0xda5842000006e711884d,0x38000040b000218805db,0x3487616a000100080331,0x8604220b20d44786a2c2,0x47622b615d0ee05f2080,0x5bc6f919101503f44cd3,0xa12c0355149099d1ae92,0x61a787214c24c408c58,0x41fc0efc374e460003,0x53994c4600030f500011,0x7fc126100b06440b849,0x2caf40240e34338033,0x6713b44c0004628d4040,0x217e937906e386f23307,0x1b0892e0fac1e7c74000],#[0x29c19800099179830803,0xe118c1dac268063d54a4,0xc2d020b844c09d42e123,0x49d0a105b2260c707a6d,0xa3192462c13782510384,0x8000d3c7001430208711,0x3236800db075dd8ac31,0x6528c1649240d682a6,0xf064c000000313ea8480,0xb85b11cc22105c000109,0x97411a5164409c3161fd,0x20703f0]]
set_option maxRecDepth 16000 in
def g251D10 := limbs80 #[#[0x58960541404c93048110,0x3fffefdfdf7f7fd8b60,0x5c822c0115008a0044c,0xb10b54862c0217600ba0,0x28a8105d842ea217316,0x494321b9124c886e2516,0x2ec437521ba105d092c6,0xc562c0a17648b020dd88,0x30dc586eca17651b928d,0x2b230dcd86e4c76262b1,0x7563b2b159586e8c7646,0x9017380b94158a02e303,0xc2ec6d6231b8185d602e,0x5c246e6e37171b838dd8,0x1055482a64017390b8c8,0x1bb2055902aa817620ab,0x5531bb08d5846aa23531,0x4257651ab28dd8c6ac63,0x8aae257612ab095504aa,0x5590aae457622ab11554,0xba95d94aaca55742bb21,0x14ab0a55452cec55762a,0xb5615aa0add8d2ac6976,0xec4b5625a992d5c56ec2,0xc5aac2d6765abb2d5c96,0xb558daae4d5626a99355,0xabab5595aae8d5646ab9,0x763a3b1ddc0eae075328,0x2f7707ab83ddd8ecec75,0x2ee6f5737ab1bddc5eae,0x1046019409603300d800,0x9827612107f03841980b],#[0x110fd07943941a80c485,0xae453228413a89384682,0x35c1a28cc06242ec16b8,0xff07ce3d21da8e6c6fe,0x849823e117489043320a,0x91554a70515278933896,0xa86333091788b785962b,0x911bd4d9a6aa34799e8c,0xfe07d83dc1e44ed874c3,0x44e22150c0848417a020,0x52ee95849e24491c08c5,0x952228553f09e34dfa67,0x6d5fcadf55caa694f6a5,0xda5d8ae6d6ecb5a599ac,0x2c591ac686253095804b,0xd696a8b4d1a2ecff669b,0x38d9c20df16e1b685b0c,0x4f1976e3b0dd44e8172b,0x3bfa5f86fa07bebd61e7,0x81830978984e09f02e80,0xc28e70217c18d10d1708,0x81830d43900418842a33,0x37031f21445020e8640e,0xe01c2382858482083868,0xc8a04e370a048201f8a8,0xc01915240f4d20885114,0x9b46a587a1e170a44a2,0x4608440008802d178992,0x8ba2b088bc50887f1309,0xc9819b7df2b5823af240,0xe822d590943fcd12f630,0x90f76503cf9487047dda],#[0x134f94960471feec4d20,0xf88626bfc3110a2fcc66,0x7fa504235e142556f02d,0x7024ebf203048ba2189c,0xfd8b135fbb15142f3414,0x20459f3d25811eac84a7,0x1c491c3ea129d98917c7,0x3045cf844abe8148aa3c,0x9f0896ac84b564253eaf,0x3559096ac84b3d258118,0x798091579809162e7012,0x3823cf5487047bbec895,0xf486116f387f11381fa4,0x48efde260661d56122c,0xa4adf6d6429237dd64b,0x848d3d5218461fb89b59,0xb56425bfb276c8a17c97,0x724241e5cfe227aff644,0x2848def3687242485f68,0x53019b7c00a11a78e168,0xc00a11b789f41423f76a,0xb81091efcc892fcc8937,0x1091afcc892efc44a3f4,0x7a7620099cbf112cf5eb,0x1f2bf21c4212b7b4122a,0x89eb78d89c567e6a0848,0x8842387da30c4cc7d661,0x115d9c0b7870c18533b3,0x38162f4bc4404254ade2,0x273fb8ec4d395bc4233b,0xd248c5f6c431331f5986,0x848f7e644835eb24595b],#[0x7ac424619c42451fa5c0,0x489cdea324245e64493d,0x1334fc1a2a47d1eb062a,0x2dcb0a35464846cff425,0x2b89a423e5f821423dcf,0x44e5e7a0d3d54e0e2493,0x413e412879f089aed98,0xab930123d9564277caf3,0xe7a4b0232fffc5880491,0x2483fe3c2269f3d25811,0x8468fb330328fe0e260,0x13d5568534bea0c631ac,0x6bbd45d1acd8a3001703,0xe7ca4b023a63294a19b4,0x228dd29178913d521c11,0xbc46370f2fc452bd6ea,0x6f83a88bbca]]
set_option maxRecDepth 16000 in
def g251H10 := limbs80 #[#[0x40300000529010f0206,0x214000e1406050301,0x20004020008000b000e,0x910010d0a0e0a020009,0x611011205091501020b,0x30102021b11090c0102,0x50000010346021b0401,0x2100030412050b000907,0x1a0905040f0b030205,0x308215b0000010a38,0x1030b03011641000e47,0x1200060106000c160000,0xd1a05030000000e0300,0x108000b050205020004,0x4c1e01072464030c0317,0x150b0000030e020845,0xb0007000a3d0d000009,0x500228300000d021d11,0x3b07130101011d110001,0x50901020a020123031d,0xb01000a050601056904,0x50e0320000200171b0b,0x2300020d070001001c,0xb000200001106910003,0x4221d4f030407020703,0x900030014090d050b,0x2000606070028022b01,0x18000501120302032900,0x20915000c04091107,0x6c684204020101010200,0x790c5a71ed26049e1c7,0x21a4108271090f698080],#[0x3e1c00020d6b6f514b0,0x320f84cc00004aacb300,0xa8b0003a95000,0x5907f000030c80008550,0xf0000d5e83f8000438c1,0x5874000b6f000083dc01,0x848b13847c4000,0x90000c6a800000000000,0x39d9b4dc000000000009,0xdc28c09931ac000c0a,0x7d03af24c008a1a00003,0x52108c316a458a2412f0,0x15e0000000a84222,0x533137075a5820000d71,0xbac9d4881e27ca650a72,0xf26c02b904ff9370b124,0xdac0001604f8dc000d09,0x5a55d603e82980008699,0xa458ce800119cfbf1352,0xc6d519ad8d813c0534ce,0x54608af8a056ff187179,0x1e53525398a1400a0269,0x842983818ab0003c1807,0x6a51845109c2dca06c23,0x17d4dc562e178000486a,0x17358000014424000f7a,0xc86c001d08bdf0876e07,0x8f4062034e186f9da145,0x33c54486603800458d6b,0x38b70609059d6760d984,0x20c3892c55ca0fd41407,0xf30003925000019b7188],#[0x430bf428711600030,0x51200f000328a443c00,0x9500000000187b93909d,0xc00003728d3cc6576103,0xa82506060ec543c000c5,0x49bc0000001ca0c53,0xc8510d2000007587a4,0x6524718fc91c0a2c87c0,0x25643303577106625,0x6a0000000000028ac,0x3927c000123a000102f0,0xe201a4f30e435bdd1b46,0x408b6c329f0a19c4f460,0xee047aa52c4149f484fb,0xb032e81247af95300cb5,0xe209e6bf6b8064c7dd13,0x1d010300000000003004,0x99603963109bc1a50f6c,0x51b26283a1a89edc68c3,0xb2c50c3e2e,0x433568e13b8,0xf1a1bdc087230c800000,0xc0b800040d0000a02952,0x75123c8b65d3c5d8000,0x280004743a1444bd19e9,0x3c5e43d10e2f04f915c1,0x954067e1ef1549612000,0xd4f401514d800017a2,0x4235f696c9e405ec1d80,0x20720001269499d18,0x116d81592778237d9e,0x816914fc3441600],#[0x724b0000000f5c242300,0x5df0000000000011bc67,0x11a8d10cc2910d4,0x2d23a246971c0007a6c0,0x35a4c81e460422211,0x2b820000000cf4474000,0x8598000495c0009,0xc1a90a040ec00000,0x4710449d668000000,0xb5059d25fc5a80000000,0x1958400096a400000010,0xb96c42a000120ac1b813,0xf895986850f053,0x1800000031ab823d69d0,0x2161918800004,0x6a645285d8d3b3c6a000,0x119c72ed79f6bd,0x1bae9301bb00000,0x4788000f6c4000000000,0x9d42710774000c210000,0x843800010c74da7,0x11dc4328081da7de9800,0x2117000,0xac000000084a400089a0,0x585c4000000015206610,0x8594e6c923560a00010e,0x6cf9ea49cc00088c2196,0x2509202a7298039c0004,0x20be877f1e688e400006,0xa51405c78100542f,0x8f0000000c1cc0000504,0x100022800000000c8492],#[0x65e00002a8021c322159,0x34d8000105c,0x10b300018f600000000,0xdd5bc01842d44e800000,0x178000000075b84db816,0x62741e0dfa7761c62166,0x932180fc0c723510451,0x84b369e77f0000629518,0x12900000000395f5d9,0x9e63c000000000001d30,0xaa6c9a9158d2537a2716,0x5d40000153402f434456,0x3f1a88000000221d0003,0x80002289c55558f0a301,0x4490000000083f000025,0xa6a28ef66c00000005c8,0x64000a97b1da283506bc,0x31e7000101d79610e128,0x87957bc85518b057,0x30c000086340000000,0x500b000087da1d800000,0x83e40008174000c1df5a,0xa6a1f2c1e548f0000000,0x4a4dd8a9f1214a8c2961,0xd21780c00000a34000c1,0x2082a4c000d14901a4a4,0x2836d1461aa1e22a01b6,0x5ca7b114000106800032,0x79b400058d4000c69fd7,0x1221746b120c21e25b,0x46d102078e71f00,0x1ee20540008a9000000],#[0x255564088483c8000c5a,0x3e88c86a7f64d1ca43a1,0xc653d96000023600032,0x31f174000340a40a800,0x79a1c1c3a800083ff0ed,0xd263343c2a4649111513,0x11ffb95697408,0x146f7ac1def707172000,0xa1e16f01645771e184b7,0x6890b07c1034248804ba,0xc631e3385ee97d0945dc,0x19d19751780ab08f001e,0x6c0009833085c9d31b1b,0x85b0000096403160af0a,0x25d00032a0c9c2553031,0x3d48fc000c7e8000409c,0xf415ecfe1a8641b159f2,0x697199978b14847ec09,0x11bd83025d0405c000,0xc139e0800000000,0x11560a17a03000109a00,0x27a000000047f80d5000,0x9c7908000a7cb2064671,0x47d00007175a0800002,0xf91a61c517f04404ac00,0xcd61676dfe5a000210b,0x5d697000317e00000008,0x118502d120b22194ed85,0x22b567a04925490b8000,0x1166131e300034a14925,0x7000306c7a51093b6db2,0x45f40000020000000312],#[0x342965817c000124d26a,0x305500021f3c935a7fc,0x19b80003dc2b3fc09800,0xdee00000000003448000,0x6500016a3000125cb6e8,0xfda6400006c302112482,0xc3c4000000158583efd9,0x7d7906c404407e4dda0c,0xbaf6d74324,0xa107d85c000000000000,0x108503000007ab45002a,0x64c00c00031ce8a40888,0x8ea38541498943f4826d,0x31320141673c91418,0x249018aa0588208e56,0xd8cfc4648ce88939dbe0,0x6078f964dbbc35e1e506,0x59844f503783f423861d,0x73c18d45156811cc77a1,0x1834000780c000c8df5,0xd8b02260001615084000,0xfa3b009,0xa4000c7081a988cc0000,0xc5f43a61690001213f3,0xdfb000002d0000000000,0x98c36b0dda11317718f9,0x4454196900031ce051f6,0xc9980008940000c18561,0x6414288bf03f0000d67,0x519eb0a4be66f2ba2874,0x1f8410400007,0xe41e1fd000],#[0xd574000d8380008290,0xcc250000000000000000,0x3065011e25400000f,0x552e710000000e04c000,0x50000c27a1bf67a00009,0x1263327b4a01746619c0,0xa2108303d7494b6e,0x79d7af42b393d07032fc,0x3000000044a216e0003a,0xc457e20000000000021a,0x30679775951d9a4000,0x4c0d800031cd89f40000,0x30b28749a6307021d509,0x11ad7689413560a12c33,0x4f06c000a0580000a95,0x5000000008c400015c11,0xaa1b08cd0700c2419920,0x4980000a44000712917c,0x211496a1697c566c841c,0x240000000f06800019,0xd5a00011ad0000000000,0x86b800046f000087b6,0x21d90000135a52c0,0xc01d9020000000000000,0x226e00000000003102,0xa0000715f14c0a5527e0,0x816cf56400058c55d247,0x3095d05396c492,0x2308ec0ef968562e9100,0x8c6e20a8406027500032,0xa7d4000e4820bb00000f,0x8a2c00044621c5],#[0xc2b40000,0x2035000000000001c300,0x139104dc1dc350193000,0x42d880800000002608,0xa422cd04000000000000,0x47dcc3184d53eb4be07,0xd5c582d06f,0xfbc77d4f1229d01a5490,0x80004a8506048628b841,0xdb2962cdc495b916f837,0x7f883810a868a0b90003,0x76605130404fdbfa7bc1,0xf5b626b0002c69000029,0x44ecb2000302900015ad,0x2800058e39f7642f97e0,0x18cac78898400006,0x7fb717c534294000c56,0x22592166755e860002,0x219024c81cf00ac0,0x10a5d6c102089000000,0x2e905499b000056e258e,0xda4a3721be5a501912,0x24ad457d272392f00e00,0x0,0x2ee37800000001d70000,0x9e0fb04300035b344371,0x41352278a98a1c04011f,0x8c048c8b0d800003cc2,0x265ec964c1e82580000,0x21a441ed02580d90bd00,0x5792734000833b281610,0xd1d41c00043e800071eb],#[0x94440000367000000011,0x84d816b000000000004d,0x90525205eb96b65850b0,0x56af03ca42a89c8,0x58f50002cfa000000000,0x1ac39705a2a6c203af61,0x127817518af04cc445,0xc4304000e60e11ca7c40,0x253a437200c000269,0x83fd9de76100a0000140,0xa0dbf2d716498b52439,0x25fc25e41155aaca,0x22488b815ba3a,0x7a000000043bb0c93158,0x2000029d49b400000039,0xc2441738837de50000a9,0x5a541753735a32a260c4,0x1344a8a5b90a111afd,0x1e34390c24f080be3600,0x2033284d1386dd097000,0x76d60097680e545df39a,0x5e7801b907278f3406e2,0xf9f04090001a9cc9ff12,0x25a8d97659947b1cc1]]
def g251D11 := limbs80 #[#[0xb60581505013048110ff,0xe574134201300d89624c,0x1785818306139e8e7d6,0x80618150511820703020,0x39f380c005694070029d,0x80198018b80a8019fd00,0x1]]
def g251H11 := limbs80 #[#[0xe04481082410a3208303,0x7c604000c68124b40020,0x45091c00a050a048850a,0xa86060a405040c400060,0x8f8428d8100040830c08,0x80e84e818084c4,0x3cc15a7f06686c30dc17,0x640d019000622148d701,0x71c81187576d63875836,0x4a932563458201000057,0xc83f07161905e41387d3,0xb76403000c30c4027d14,0xc55e36000a77081276,0x65d069d17000000d5e0,0x65402a83e00060900046,0x4442ec0283343bb77842,0x7be67965000a5e0009,0xc7700091387c940c3500,0x4f44c93e000853e40437,0xd41e4c0008074,0xd0281c00000000000,0x1a578147000050748000,0x5000000e5116001241fc,0x1ba8086d02d00000084,0x2c235000441d4ec56b62,0xd278c4887f610c49c748,0x820000063a6ed6d50563,0x78073f0a101482f1004a,0x8072c5c34342200084dc,0x87e467000000177c59c3,0x10065c5100010376783c,0x100a825c340004280004],#[0xb7800bc5d42be0a77022,0x1d82f931004829e39162,0x5026a55000000d040360,0x83e7e000000a05363d4,0x3183241406400070b079,0x200000084b0000000006,0x846427241f57000861f0,0xa6643d016000031,0x443100000000000b490,0x50ac5f55d00000,0x10f31000000000000a2c,0x8b1705a00000046bc765,0xe2613d80f000f1b005c6,0x64c6a000000c39000444,0x8000000000408000e527,0x80c000c8000000070,0x47c62c5b83ac23000000,0x2400000020c3688013,0x63e00600000000000000,0x44766dd5f000f3c000,0x9f1305400023b07a0,0x40054dc6fb29d4301e47,0xc52021000b1dd7686e]]
def g251D12 (j : Nat) := if j=0 then 0x5080c1010037f else 0
def g251H12 := limbs80 #[#[0x44028,0x80198000000000314000,0x10fc,0x188000000000001080,0x2c4942001840,0x24800000002d750000,0x2640000000,0x30000000000000,0xc0000000004000000000,0x4,0x31800000000000,0x160000000001c03100,0x540000000000000,0x15825d802800]]
def g251L : Nat → Packing
  | 6 => (2,6,7,0,0,6,0,g251D6)
  | 7 => (79,5,7,2359364,103,12,1126,g251D7)
  | 8 => (622,4,7,6619433,121,15,1256,g251D8)
  | 9 => (680,3,7,2490478,103,15,1163,g251D9)
  | 10 => (132,2,7,393226,52,13,1100,g251D10)
  | 11 => (10,1,7,65537,0,8,1039,g251D11)
  | 12 => (1,0,7,0,0,0,0,g251D12)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupShort 1 2 0 3 1 0 g251H7
  | 8 => lookupShort 38 167 7 11 7 2 g251H8
  | 9 => lookupShort 255 1163 10 14 10 2 g251H9
  | 10 => lookupShort 296 1613 8 14 10 2 g251H10
  | 11 => lookupShort 60 331 7 12 8 2 g251H11
  | 12 => lookupShort 6 139 1 8 4 2 g251H12
  | _ => fun _ => none
def g251 : Forest := ⟨251,12,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_0 : block g251 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B6 : block g251 6 0 2=true := g251P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_0 : block g251 7 0 63=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_63 : block g251 7 63 16=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B7 : block g251 7 0 79=true := (@block_merge g251 7 0 63 16 g251P7_0 g251P7_63)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 41=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_41 : block g251 8 41 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_137 : block g251 8 137 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_233 : block g251 8 233 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_329 : block g251 8 329 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_425 : block g251 8 425 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_521 : block g251 8 521 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_528 : block g251 8 528 94=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 622=true := (@block_merge g251 8 0 329 293 (@block_merge g251 8 0 137 192 (@block_merge g251 8 0 41 96 g251P8_0 g251P8_41) (@block_merge g251 8 137 96 96 g251P8_137 g251P8_233)) (@block_merge g251 8 329 192 101 (@block_merge g251 8 329 96 96 g251P8_329 g251P8_425) (@block_merge g251 8 521 7 94 g251P8_521 g251P8_528)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_4 : block g251 9 4 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_100 : block g251 9 100 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_196 : block g251 9 196 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_292 : block g251 9 292 43=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_335 : block g251 9 335 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_431 : block g251 9 431 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_527 : block g251 9 527 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_623 : block g251 9 623 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_659 : block g251 9 659 21=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 680=true := (@block_merge g251 9 0 335 345 (@block_merge g251 9 0 100 235 (@block_merge g251 9 0 4 96 g251P9_0 g251P9_4) (@block_merge g251 9 100 96 139 g251P9_100 (@block_merge g251 9 196 96 43 g251P9_196 g251P9_292))) (@block_merge g251 9 335 192 153 (@block_merge g251 9 335 96 96 g251P9_335 g251P9_431) (@block_merge g251 9 527 96 57 g251P9_527 (@block_merge g251 9 623 36 21 g251P9_623 g251P9_659))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : block g251 10 0 59=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_59 : block g251 10 59 73=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 132=true := (@block_merge g251 10 0 59 73 g251P10_0 g251P10_59)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_0 : block g251 11 0 10=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B11 : block g251 11 0 10=true := g251P11_0
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
theorem g251G : graphValid g251 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 13 := lower_forest (g:=g251) (i:=0) (hints:=65603) (before_sound K235 V235) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K235 13 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V235 low251 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 sevenInputs.toFinset := by
  change Impossible true (graphGoal 255) 13 sevenInputs.toFinset
  exact cut_root (m:=255) (before_sound K251 V251) (4, 0, 251, 0, 13) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_52262

open PEqualNP.Outside.L_meta_52262 in
theorem PEqualNP.Outside.L_meta_52262 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

import PEqualNP.Defs
-- Fixing vertex 5 to zero saves one gate. On the eleven remaining vertices
-- a monotone circuit needs at least eighteen gates. Even with free inversions
-- a circuit needs at least seventeen binary gates.
-- The live-circuit, restriction and rectangle arguments adapt project proofs
-- L-meta-670 and L-meta-9818. The graph and all finite tables are specific to this proof.
namespace PEqualNP.Outside.L_meta_9752
namespace Engine
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 2048
def zero : Sig := 0
def one : Sig := BitVec.allOnes 2048
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
def bit (i : Fin 2048) (a : Sig) : Bool := a.getLsbD i.val
theorem bit_zero (i) : bit i zero = false := by simp [bit,zero]
theorem bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
theorem bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
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
theorem get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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
theorem extract {u target} (gs : List Gate) (w : List Sig)
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
abbrev Row := Fin 2048
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
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffefffefffffffefffffffefffffffefffefffefffffffefffffffefffffffefffffffefffffffefffffffefffffefefffffefefffffffafffffffafffffffafffafffafffffffafffffffafffffafafafafafafffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffefffeffffffeeffffffeeffffffeeffeeffeefffffffefffffffcfffffffefffffffcfffffffefffffffcfffffefefffffcfcfffffffafffffff0fffffffafff0fff0ffffffaaffffff00ffffaaaa00000000
def sample (r : Row) (j : Fin 11) := bit r (inputs.getD j.val zero)
def edge (x : Fin 11 → Bool) : Bool :=
  (x 0 && x 5) || (x 0 && x 9) || (x 0 && x 10) || (x 1 && x 8) || (x 1 && x 9) || (x 2 && x 7) || (x 2 && x 8) || (x 2 && x 10) || (x 3 && x 6) || (x 3 && x 7) || (x 3 && x 9) || (x 4 && x 5) || (x 4 && x 6) || (x 4 && x 8)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 11 => inputs.getD j.val zero) = inputs := rfl
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
abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 2048-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(2048-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 2048 (2048-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)
theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 2048-d.val <;> simp [shifted,h,r.isLt]
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
  (List.range 11).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def varsX (m : Nat) := vars m
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero

def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 5) ||| (x 0 &&& x 9) ||| (x 0 &&& x 10) ||| (x 1 &&& x 8) ||| (x 1 &&& x 9) ||| (x 2 &&& x 7) ||| (x 2 &&& x 8) ||| (x 2 &&& x 10) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 3 &&& x 9) ||| (x 4 &&& x 5) ||| (x 4 &&& x 6) ||| (x 4 &&& x 8)
def subcube (z o : Nat) : Sig :=
  if z &&& o != 0 then zero else
    (List.range 11).foldl (fun w i => if z.testBit i then w &&& ~~~(inputs.getD i zero)
      else if o.testBit i then w &&& inputs.getD i zero else w) one
def fixRows (z o : Nat) : List Move :=
  (List.range 11).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 2048 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 2048 d)
def supportPairs (_t mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 2048 (1 <<< i))
def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 2048 r,Fin.ofNat 2048 (r ||| (1 <<< i)))
def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 2048+2048*(c.1/2048)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 2048) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/2048+80) s
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
  let free := colFree raw (z % 2048) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/2048+80) s
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
abbrev Bits := BitVec 320
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals
def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 320 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 320 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 320 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 320 → Row) (x : Decor) := x.2 = pairSig r s x.1
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
    let a := ws.getD (bits &&& 31) defaultDecor
    let b := ws.getD ((bits >>> 5) &&& 31) defaultDecor
    decodeBank k (bits >>> 12) (ws++[dbin ((bits >>> 10) &&& 3) a b])
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
def asRow (cols : Nat → Bits) (i : Fin 320) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 11 => (cols j.val).getLsbD i.val))).toFin.cast
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
theorem coordinate9 : ∀ r : Row, bit r (inputs.getD 9 zero) = r.val.testBit 9 := by decide +kernel
theorem coordinate10 : ∀ r : Row, bit r (inputs.getD 10 zero) = r.val.testBit 10 := by decide +kernel
theorem input_coords : ∀ (j : Fin 11) (r : Row), bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j
  fin_cases j
  · exact coordinate0
  · exact coordinate1
  · exact coordinate2
  · exact coordinate3
  · exact coordinate4
  · exact coordinate5
  · exact coordinate6
  · exact coordinate7
  · exact coordinate8
  · exact coordinate9
  · exact coordinate10
theorem asRow_bit (cols : Nat → Bits) (i : Fin 320) (j : Fin 11) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 11 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<11 ∧ a=inputs.getD j zero := by
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
  (x 0 &&& x 5) ||| (x 0 &&& x 9) ||| (x 0 &&& x 10) ||| (x 1 &&& x 8) ||| (x 1 &&& x 9) ||| (x 2 &&& x 7) ||| (x 2 &&& x 8) ||| (x 2 &&& x 10) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 3 &&& x 9) ||| (x 4 &&& x 5) ||| (x 4 &&& x 6) ||| (x 4 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 320) (j : Fin 11) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 320) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<11) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide),pos 9 (by decide),pos 10 (by decide)]
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
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
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
    if (rs ||| column d z.2) != BitVec.allOnes 320 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 320) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 320 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
  by_cases hj : j<11
  · let i : Fin 11 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 2048 ≤ 2^j := by
      change 2^11 ≤ 2^j
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
abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 12)
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 320) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 320) (hq : chartSamples m q = 0) :
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
def forestRecord (tab : Packing) (_raw i : Nat) :=
  let (_,_,_,_,_,_,_,words) := tab
  words (2*i)
def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 12*storedDepth g depth
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
    let more := chosenSteps bank (ops >>> 12) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 10 2,(bank.getD (ops &&& 31) defaultDecor).1,
        (bank.getD (getFieldV ops 5 5) defaultDecor).1) :: more
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
def decodeHints (cw d : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,x => (x % (1 <<< cw),(x >>> cw) % (1 <<< d)) ::
      decodeHints cw d n (x >>> (cw+d))
def forestHints (tab : Packing) (_raw i : Nat) :=
  let (_,depth,cw,_,_,_,_,words) := tab
  let data := words (2*i+1)
  decodeHints cw depth (data % 256) (data >>> 8)
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

def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 320) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))
def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^321*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^321 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<321 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<321 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<321 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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
def fullMarks (r packed : Nat) := ((packed+r) >>> 320) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (321*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^321)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 321*(i+1)-321=321*i := by omega
      have ge : ¬321*(i+1)<321 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 320 = (a==BitVec.allOnes 320) := by
  by_cases h : a=BitVec.allOnes 320
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^320-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^320 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (321*i) =
      (f xs[i]==BitVec.allOnes 320) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^321*u+x+(2^321*v+1)=2^321*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^321 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬321*(i+1)+320<321 := by omega
      have di : 321*(i+1)+320-321=321*i+320 := by omega
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 321) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (321*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 321) (i:=i) (by simpa using hi) _ ok.2
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
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
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
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 11)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem swap_table : ∀ v : Fin 176, validSwap v.val=true → ∀ t : Fin 11, swapIdx v.val t.val<11 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<11) : swapIdx v t<11 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<176 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<11) :
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
  | n+1,bits,ws => force (zN ((bits >>> 10) &&& 3) (ws.getD (bits &&& 31) 0) (ws.getD ((bits >>> 5) &&& 31) 0))
      fun z => decodeN n (bits >>> 12) (ws++[z])
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
  let len := 12*depth
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
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 320 then true
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
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 320
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

structure KWRooms (S : Finset Sig) (T : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n
def kwLeaf (T : Sig) : KWRooms {T} T where
  owns v p n := v=T ∧ bit p T=true ∧ bit n T=false
  total p n hp hn := ⟨T,rfl,hp,hn⟩
  valid := by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,hp,hn⟩
  unique := by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm
  rect := by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩
def kwFork {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : KWRooms (insert (bin d a b) U) T) : KWRooms (insert a (insert b U)) T := by
  let z := bin d a b
  let sel := fun p n : Row => if d=0 then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin 0 a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin 1 a b) = (bit r a || bit r b) := by simp [bin,bit]
    rcases d01 with e | e <;> cases pA : bit p a <;> cases nA : bit n a <;>
      simp_all [sel,z]
  refine { owns := fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
           total := ?_
           valid := ?_
           unique := ?_
           rect := ?_ }
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with eq | mem
    · have vz : v=z := eq
      refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
      rw [←vz]
      exact hv
    · exact ⟨v,Or.inl ⟨mem,hv⟩⟩
  · intro v p n h
    rcases h with ⟨mem,hv⟩ | ⟨e,hv⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),(H.valid hv).2⟩
    · subst v
      have inS : sel p n ∈ insert a (insert b U) := by
        rcases pick p n with eq | eq <;> simp [eq]
      exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact H.unique hv hw
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hv hw]
      exact vU
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hw hv]
      exact wU
    · exact ve.trans we.symm
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact False.elim (outside p' n (we ▸ vU))
    · exact False.elim (outside p n' (ve ▸ wU))
    · refine Or.inr ⟨?_,H.rect hv hw⟩
      by_cases h : d=0
      · simpa only [sel,h,ite_true] using we
      · simpa only [sel,h,ite_false] using ve
theorem kwWidth {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega
theorem kwTight {T k S} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨kwLeaf T⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b∉U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := kwWidth tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le (a:=a) (insert b U)
    have le2 := Finset.card_insert_le (a:=b) U
    have ha : a∉U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a∈insert b U)] at tight
      omega
    have hb : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by rcases hd with h | ⟨h,_⟩ <;> simp_all <;> omega
    exact ⟨kwFork d01 ha hb fresh H⟩
def onlyWire (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, bit p w=true → bit n w=false → w=v
theorem kwOwn {S T v p n} (H : KWRooms S T) (one : onlyWire S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2.1 (H.valid hw).2.2
  exact eq ▸ hw
theorem kwCross {S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : onlyWire S T a p na) (B : onlyWire S T b p nb)
    (C : onlyWire S T a pa n) (D : onlyWire S T b pb n) : Impossible false T k S := by
  intro j hj run
  have lb := kwWidth run
  have tight : S.card=j+1 := by omega
  obtain ⟨H⟩ := kwTight run tight
  exact different (H.unique (H.rect (kwOwn H A) (kwOwn H C)) (H.rect (kwOwn H B) (kwOwn H D)))
def kwWireB (ws : List Sig) (T v : Sig) (p n : Row) : Bool :=
  bit p T && !bit n T && ws.all (fun w => !bit p w || bit n w || w==v)
theorem kwWireB_sound {ws T v p n} (h : kwWireB ws T v p n=true) :
    onlyWire ws.toFinset T v p n := by
  simp only [kwWireB,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw hp hn
  simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using
    h.2 w (List.mem_toFinset.mp hw)
def kwWord (T : Sig) (ws : List Sig) (k value : Nat) : Bool :=
  let a := ws.getD (value % 16) zero
  let b := ws.getD ((value >>> 4) % 16) zero
  let row := fun i : Nat => Fin.ofNat 2048 ((value >>> (8+11*i)) % 2048)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    kwWireB ws T a (row 0) (row 2) && kwWireB ws T b (row 0) (row 3) &&
    kwWireB ws T a (row 4) (row 1) && kwWireB ws T b (row 5) (row 1)
theorem kwWord_sound {T ws k v} (h : kwWord T ws k v=true) : Impossible false T k ws.toFinset := by
  simp only [kwWord,Bool.and_eq_true,decide_eq_true_eq] at h
  exact kwCross h.1.1.1.1.1 h.1.1.1.1.2 (kwWireB_sound h.1.1.1.2)
    (kwWireB_sound h.1.1.2) (kwWireB_sound h.1.2) (kwWireB_sound h.2)
def CutRow (g : Forest) (k start n : Nat) : Prop :=
  ∀ j, start≤j → j<start+n → nodeVerified g k j=true ∨ Impossible g.mode (targetOf g) k (stateSet g k j).toFinset
theorem mixedEmpty (g : Forest) (k a : Nat) : CutRow g k a 0 := by
  intro j lo hi
  omega
theorem checkedRow {g k a n} (h : block g k a n=true) : CutRow g k a n :=
  fun j lo hi => Or.inl (block_at h j lo hi)
theorem joinRow {g k a x y} (first : CutRow g k a x) (last : CutRow g k (a+x) y) :
    CutRow g k a (x+y) := by
  intro j lo hi
  by_cases e : j<a+x
  · exact first j lo e
  · exact last j (by omega) (by omega)
def kwTest (g : Forest) (k a n : Nat) (data : Nat → Nat) :=
  (List.range n).all fun j => kwWord (targetOf g) (stateSet g k (a+j)) k (data j)
theorem mixedCut {g k a n data} (mode : g.mode=false) (h : kwTest g k a n data=true) :
    CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have sum : a+(j-a)=j := by omega
  change kwWord _ (stateSet g k (a+(j-a))) k _=true at hh
  rw [sum] at hh
  exact kwWord_sound hh
def mixedTables (g : Forest) (top : Nat) := ∀ k ≤ top, CutRow g k 0 (g.levels k).1
theorem mixedForest (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior=true) (rows : mixedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    rcases rows 0 hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) checked
    · exact done
  | succ k ih =>
    intro hk i hi
    rcases rows _ hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
        (fun _ => by simpa using ih (by omega)) checked
    · exact done
theorem mixedRoot {g top prior k i ws} (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : mixedTables g top) (le : k≤top)
    (idx : indexedRoot g k i ws=true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact mixedForest g top prior lower geom blocks _ le i idx.1
theorem mixedLower {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : mixedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (mixedRoot low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
structure FreeRooms (S : Finset Sig) (T H : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false →
    (bit p H=true ∧ bit n H=false) ∨ ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

structure SingleFactor (S : Finset Sig) (T : Sig) where
  inner : Finset Sig
  outer : Finset Sig
  pivot : Sig
  cover : inner ∪ outer = S
  apart : Disjoint inner outer
  inside : KWRooms inner pivot
  outside : FreeRooms outer T pivot
def freeFrom {S T} (D : KWRooms S T) (h : Sig) : FreeRooms S T h where
  owns := D.owns
  total p n hp hn := Or.inr (D.total p n hp hn)
  valid := D.valid
  unique := D.unique
  rect := D.rect
def freeHide {S T h} (D : FreeRooms S T h) : FreeRooms (S.erase h) T h where
  owns v p n := v≠h ∧ D.owns v p n
  total := by
    intro p n hp hn
    rcases D.total p n hp hn with yes | ⟨v,hv⟩
    · exact Or.inl yes
    · by_cases eq : v=h
      · exact Or.inl (eq ▸ (D.valid hv).2)
      · exact Or.inr ⟨v,eq,hv⟩
  valid := by
    rintro v p n ⟨ne,hv⟩
    exact ⟨Finset.mem_erase.mpr ⟨ne,(D.valid hv).1⟩,(D.valid hv).2⟩
  unique := fun h1 h2 => D.unique h1.2 h2.2
  rect := fun a b => ⟨a.1,D.rect a.2 b.2⟩
def factorOfTree {S T} (D : KWRooms S T) : SingleFactor S T where
  inner := S
  outer := ∅
  pivot := T
  cover := by simp
  apart := by simp
  inside := D
  outside := {
    owns := fun _ _ _ => False
    total := fun p n hp hn => Or.inl ⟨hp,hn⟩
    valid := fun h => h.elim
    unique := fun h _ => h.elim
    rect := fun h _ => h.elim }
def freeFork {h : Sig} {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : FreeRooms (insert (bin d a b) U) T h) : FreeRooms (insert a (insert b U)) T h := by
  let z := bin d a b
  let sel := fun p n : Row => if d=0 then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin 0 a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin 1 a b) = (bit r a || bit r b) := by simp [bin,bit]
    rcases d01 with e | e <;> cases pA : bit p a <;> cases nA : bit n a <;>
      simp_all [sel,z]
  refine { owns := fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
           total := ?_
           valid := ?_
           unique := ?_
           rect := ?_ }
  · intro p n hp hn
    rcases H.total p n hp hn with closed | ⟨v,hv⟩
    · exact Or.inl closed
    right
    rcases Finset.mem_insert.mp (H.valid hv).1 with eq | mem
    · have vz : v=z := eq
      refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
      rw [←vz]
      exact hv
    · exact ⟨v,Or.inl ⟨mem,hv⟩⟩
  · intro v p n h
    rcases h with ⟨mem,hv⟩ | ⟨e,hv⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),(H.valid hv).2⟩
    · subst v
      have inS : sel p n ∈ insert a (insert b U) := by
        rcases pick p n with eq | eq <;> simp [eq]
      exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact H.unique hv hw
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hv hw]
      exact vU
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hw hv]
      exact wU
    · exact ve.trans we.symm
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact False.elim (outside p' n (we ▸ vU))
    · exact False.elim (outside p n' (ve ▸ wU))
    · refine Or.inr ⟨?_,H.rect hv hw⟩
      by_cases h : d=0
      · simpa only [sel,h,ite_true] using we
      · simpa only [sel,h,ite_false] using ve
theorem supportSide {A B U : Finset Sig} {a b z : Sig}
    (e : A∪B=insert z U) (disj : Disjoint A B) (za : z∈A)
    (freshA : a∉insert z U) (freshB : b∉insert z U) (freshZ : z∉U) :
    (insert a (insert b (A.erase z))) ∪ B=insert a (insert b U) ∧
    Disjoint (insert a (insert b (A.erase z))) B ∧ a∉A.erase z ∧ b∉A.erase z := by
  have hb : z∉B := fun h => Finset.disjoint_left.mp disj za h
  have allmem (w : Sig) : w∈A∨w∈B ↔ w=z∨w∈U := by
    rw [←Finset.mem_union,←Finset.mem_insert,e]
  have aout : a∉A ∧ a∉B := by
    have h : a∉A∪B := by rw [e]; exact freshA
    simpa using h
  have bout : b∉A ∧ b∉B := by
    have h : b∉A∪B := by rw [e]; exact freshB
    simpa using h
  refine ⟨?_,?_,fun h => aout.1 (Finset.mem_of_mem_erase h),fun h => bout.1 (Finset.mem_of_mem_erase h)⟩
  · ext w
    have m := allmem w
    by_cases eq : w=z
    · subst w; simp [freshZ,hb]
    · simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_erase] at *
      tauto
  · apply Finset.disjoint_left.mpr
    intro w hw hwB
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact aout.2 hwB
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact bout.2 hwB
    exact Finset.disjoint_left.mp disj (Finset.mem_of_mem_erase hw) hwB
def factorExpand {U T a b d} (hd : d=0 ∨ d=1)
    (freshA : a∉insert (bin d a b) U) (freshB : b∉insert (bin d a b) U)
    (freshZ : bin d a b∉U) (F : SingleFactor (insert (bin d a b) U) T) :
    SingleFactor (insert a (insert b U)) T := by
  classical
  let z := bin d a b
  by_cases inn : z∈F.inner
  · obtain ⟨eq,apart,ha,hb⟩ := supportSide F.cover F.apart inn freshA freshB freshZ
    have old : KWRooms (insert z (F.inner.erase z)) F.pivot := by
      rw [Finset.insert_erase inn]; exact F.inside
    exact ⟨_,F.outer,F.pivot,eq,apart,kwFork hd ha hb (by simp [z]) old,F.outside⟩
  · have out : z∈F.outer := by
      have m : z∈F.inner∪F.outer := by rw [F.cover]; exact Finset.mem_insert_self _ _
      exact (Finset.mem_union.mp m).resolve_left inn
    obtain ⟨eq,apart,ha,hb⟩ := supportSide ((Finset.union_comm _ _).trans F.cover) F.apart.symm out freshA freshB freshZ
    have old : FreeRooms (insert z (F.outer.erase z)) T F.pivot := by
      rw [Finset.insert_erase out]; exact F.outside
    exact ⟨F.inner,_,F.pivot,(Finset.union_comm _ _).trans eq,apart.symm,F.inside,
      freeFork hd ha hb (by simp [z]) old⟩
def factorKeep {U T a b d} (hd : d=0 ∨ d=1) (ab : a≠b) (hb : b∉U)
    (fresh : bin d a b∉insert a (insert b U)) (H : KWRooms (insert (bin d a b) U) T) :
    SingleFactor (insert a (insert b U)) T := by
  let z := bin d a b
  have za : z≠a := by
    intro eq
    apply fresh
    exact Finset.mem_insert.mpr (Or.inl eq)
  have zU : z∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have set0 : (insert z U).erase a = insert z (U.erase a) := by
    ext v
    simp only [Finset.mem_erase,Finset.mem_insert]
    by_cases eq : v=z
    · subst v; simp [za]
    · tauto
  have H0 : FreeRooms (insert z (U.erase a)) T a := set0 ▸ freeHide (freeFrom H a)
  have H1 := freeFork hd (show a∉U.erase a by simp)
    (fun m => hb (Finset.mem_of_mem_erase m)) (fun m => zU (Finset.mem_of_mem_erase m)) H0
  have eq : insert a (insert b (U.erase a))=insert a (insert b U) := by
    ext v
    simp only [Finset.mem_insert,Finset.mem_erase]
    tauto
  have H1' : FreeRooms (insert a (insert b U)) T a := eq ▸ H1
  refine ⟨{a},(insert a (insert b U)).erase a,a,?_,?_,kwLeaf a,freeHide H1'⟩
  · ext v; simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_erase,Finset.mem_insert]; tauto
  · simp
theorem oneShare {T k S} (r : Live false T k S) (budget : k≤S.card) :
    Nonempty (SingleFactor S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := r
    exact ⟨factorOfTree (kwLeaf T)⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,ab,fresh,tail⟩ := r
    let z := bin d a b
    have zU : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have size := kwWidth tail
    have zcard : (insert z U).card=U.card+1 := Finset.card_insert_of_notMem zU
    change (insert z U).card ≤ k+1 at size
    have hd01 : d=0 ∨ d=1 := by rcases hd with q | ⟨q,_⟩ <;> simp_all <;> omega
    by_cases ain : a∈U
    · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ain : a∈insert b U)] at budget
      by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin'] at budget; omega
      · rw [Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨H⟩ := kwTight tail (by change (insert z U).card=k+1; omega)
        exact ⟨factorKeep hd01 ab bin' fresh H⟩
    · by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin',Finset.card_insert_of_notMem ain] at budget
        obtain ⟨H⟩ := kwTight tail (by change (insert z U).card=k+1; omega)
        have comm : bin d b a=z := by
          rcases hd01 with eq | eq <;> subst d <;> simp [z,bin,BitVec.and_comm,BitVec.or_comm]
        have H' : KWRooms (insert (bin d b a) U) T := by simpa only [comm] using H
        have fr : bin d b a∉insert b (insert a U) := by simpa only [comm,Finset.insert_comm] using fresh
        have F := factorKeep hd01 ab.symm ain fr H'
        exact ⟨by simpa only [Finset.insert_comm] using F⟩
      · have an : a∉insert b U := by simp [ain,ab]
        rw [Finset.card_insert_of_notMem an,Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨F⟩ := ih tail (by change k≤(insert z U).card; omega)
        have neA : a≠z := fun e => fresh (Finset.mem_insert.mpr (Or.inl e.symm))
        have neB : b≠z := fun e => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e.symm)))
        have fa : a∉insert z U := fun h => (Finset.mem_insert.mp h).elim neA ain
        have fb : b∉insert z U := fun h => (Finset.mem_insert.mp h).elim neB bin'
        exact ⟨factorExpand hd01 fa fb zU F⟩
theorem factorForced {S : Finset Sig} {T : Sig} (F : SingleFactor S T) (p n : Row)
    (hp : bit p T=true) (hn : bit n T=false)
    (none : ∀ v∈F.outer, bit p v=true → bit n v=false → False) :
    bit p F.pivot=true ∧ bit n F.pivot=false := by
  rcases F.outside.total p n hp hn with h | ⟨v,hv⟩
  · exact h
  · exact False.elim (none v (F.outside.valid hv).1 (F.outside.valid hv).2.1 (F.outside.valid hv).2.2)
theorem factorOuterOwn {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a p n} (ao : a∈F.outer)
    (one : onlyWire S T a p n) : F.outside.owns a p n := by
  rcases F.outside.total p n one.1 one.2.1 with hpivot | ⟨w,hw⟩
  · obtain ⟨w,hw⟩ := F.inside.total p n hpivot.1 hpivot.2
    obtain ⟨wi,wp,wn⟩ := F.inside.valid hw
    have ws : w∈S := F.cover ▸ Finset.mem_union_left _ wi
    have eq := one.2.2 w ws wp wn
    rw [eq] at wi
    exact False.elim (Finset.disjoint_left.mp F.apart wi ao)
  · obtain ⟨wo,wp,wn⟩ := F.outside.valid hw
    have ws : w∈S := F.cover ▸ Finset.mem_union_right _ wo
    have eq := one.2.2 w ws wp wn
    exact eq ▸ hw
theorem outerCannotCross {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (aout : a∈F.outer) (bout : b∈F.outer)
    (different : a≠b) (A : onlyWire S T a p na) (B : onlyWire S T b p nb)
    (C : onlyWire S T a pa n) (D : onlyWire S T b pb n) : False :=
  different (F.outside.unique (F.outside.rect (factorOuterOwn F aout A) (factorOuterOwn F aout C))
    (F.outside.rect (factorOuterOwn F bout B) (factorOuterOwn F bout D)))
theorem innerCannotCross {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (different : a≠b) (A : onlyWire F.inner F.pivot a p na) (B : onlyWire F.inner F.pivot b p nb)
    (C : onlyWire F.inner F.pivot a pa n) (D : onlyWire F.inner F.pivot b pb n) : False :=
  different (F.inside.unique (F.inside.rect (kwOwn F.inside A) (kwOwn F.inside C))
    (F.inside.rect (kwOwn F.inside B) (kwOwn F.inside D)))
theorem innerSource {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {v p n}
    (hv : v∈F.inner) (only : onlyWire S T v p n) : onlyWire F.inner F.pivot v p n := by
  have h : bit p F.pivot=true ∧ bit n F.pivot=false := by
    apply factorForced F p n only.1 only.2.1
    intro w wo hp hn
    have ws : w∈S := F.cover ▸ Finset.mem_union_right _ wo
    have eq := only.2.2 w ws hp hn
    exact Finset.disjoint_left.mp F.apart hv (eq ▸ wo)
  refine ⟨h.1,h.2,?_⟩
  intro w wi hp hn
  exact only.2.2 w (F.cover ▸ Finset.mem_union_left _ wi) hp hn
theorem hornRule {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b c p n pa na}
    (ar : onlyWire S T a p na) (br : onlyWire S T b pa n) (cr : onlyWire S T c p n)
    (ia : a∈F.inner) (ib : b∈F.inner) : c∈F.inner := by
  have ah := innerSource F ia ar
  have bh := innerSource F ib br
  obtain ⟨w,hw⟩ := F.inside.total p n ah.1 bh.2.1
  obtain ⟨wi,wp,wn⟩ := F.inside.valid hw
  have ws : w∈S := F.cover ▸ Finset.mem_union_left _ wi
  exact (cr.2.2 w ws wp wn) ▸ wi
theorem parityRule {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (hs : a∈S) (ht : b∈S) (ne : a≠b)
    (h1 : onlyWire S T a p na) (h2 : onlyWire S T b p nb)
    (h3 : onlyWire S T a pa n) (h4 : onlyWire S T b pb n) :
    ((a∈F.inner ∧ b∈F.inner) ∨ (a∉F.inner ∧ b∉F.inner)) → False := by
  rintro (⟨ia,ib⟩ | ⟨oa,ob⟩)
  · exact innerCannotCross F ne (innerSource F ia h1) (innerSource F ib h2)
      (innerSource F ia h3) (innerSource F ib h4)
  · rw [←F.cover,Finset.mem_union] at hs ht
    exact outerCannotCross F (hs.resolve_left oa) (ht.resolve_left ob) ne h1 h2 h3 h4
def colorPoint (v : Fin 11 → Bool) : Row :=
  (BitVec.ofBoolListLE (List.ofFn v)).toFin.cast (by simp [List.length_ofFn])
theorem color_bit (v : Fin 11 → Bool) (i : Fin 11) :
    bit (colorPoint v) (inputs.getD i.val zero) = v i := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn v)).getLsbD i.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def colorField (d j : Nat) : Fin 11 := Fin.ofNat 11 ((d >>> (1+4*j)) % 16)
def colorRow (d j : Nat) : Row := Fin.ofNat 2048 ((d >>> (13+11*j)) % 2048)
def colorWire (ws : List Sig) (names : Nat) (j : Fin 11) : Sig :=
  ws.getD ((names >>> (4*j.val)) % 16) zero
def colorRule (ws : List Sig) (T : Sig) (names d : Nat) : Bool :=
  let a := colorWire ws names (colorField d 0)
  let b := colorWire ws names (colorField d 1)
  let c := colorWire ws names (colorField d 2)
  let r := colorRow d
  if d.testBit 0 then
    (decide (a ∈ ws) && decide (b ∈ ws) && decide (a ≠ b)) &&
    (kwWireB ws T a (r 0) (r 2) && kwWireB ws T b (r 0) (r 3) &&
      kwWireB ws T a (r 4) (r 1) && kwWireB ws T b (r 5) (r 1))
  else kwWireB ws T a (r 0) (r 2) && kwWireB ws T b (r 3) (r 1) &&
    kwWireB ws T c (r 0) (r 1)
def constraintWord (d : Nat) : Sig :=
  let x := fun j => inputs.getD (colorField d j).val zero
  if d.testBit 0 then x 0 ^^^ x 1 else ~~~(x 0 &&& x 1) ||| x 2
def colorTruth {ws : List Sig} {T : Sig} (F : SingleFactor ws.toFinset T)
    (names : Nat) (i : Fin 11) := decide (colorWire ws names i ∈ F.inner)
theorem parity_bit {A B : Prop} [Decidable A] [Decidable B]
    (h : ¬ ((A ∧ B) ∨ (¬A ∧ ¬B))) : (decide A ^^ decide B) = true := by
  by_cases a : A <;> by_cases b : B <;> simp_all
theorem horn_bit {A B C : Prop} [Decidable A] [Decidable B] [Decidable C]
    (h : A → B → C) : (!(decide A && decide B) || decide C) = true := by
  by_cases a : A <;> by_cases b : B <;> simp_all
theorem bit_xor (r : Row) (a b : Sig) : bit r (a ^^^ b) = (bit r a ^^ bit r b) :=
  BitVec.getLsbD_xor
theorem rule_valid {ws T names d} (F : SingleFactor ws.toFinset T)
    (h : colorRule ws T names d = true) :
    bit (colorPoint (colorTruth F names)) (constraintWord d) = true := by
  have bits (i) := color_bit (colorTruth F names) (colorField d i)
  by_cases flag : d.testBit 0 = true
  · simp only [colorRule,flag,ite_true,Bool.and_eq_true,decide_eq_true_eq] at h
    have rule := parityRule F (List.mem_toFinset.mpr h.1.1.1) (List.mem_toFinset.mpr h.1.1.2) h.1.2
      (kwWireB_sound h.2.1.1.1) (kwWireB_sound h.2.1.1.2) (kwWireB_sound h.2.1.2) (kwWireB_sound h.2.2)
    simp only [constraintWord,flag,ite_true]
    rw [bit_xor,bits,bits]
    exact parity_bit rule
  · simp only [colorRule,if_neg flag,Bool.and_eq_true] at h
    have rule := hornRule F (kwWireB_sound h.1.1) (kwWireB_sound h.1.2) (kwWireB_sound h.2)
    simp only [constraintWord,if_neg flag]
    change bit _ (prime true (neg (prime false _ _)) _) = true
    rw [bit_prime,bit_neg,bit_prime]
    change (!(bit _ _ && bit _ _) || bit _ _) = true
    rw [bits,bits,bits]
    exact horn_bit rule
def colorSet : List Nat → Sig
  | [] => one
  | d::ds => constraintWord d &&& colorSet ds
theorem color_set {ws T names} (F : SingleFactor ws.toFinset T) (ds : List Nat)
    (h : ds.all (colorRule ws T names) = true) :
    bit (colorPoint (colorTruth F names)) (colorSet ds) = true := by
  induction ds with
  | nil => exact bit_one _
  | cons d ds ih =>
    simp only [List.all_cons,Bool.and_eq_true] at h
    change bit _ (prime false _ _) = true
    rw [bit_prime,rule_valid F h.1,ih h.2]
    rfl
def colorCheck (ws : List Sig) (T : Sig) (k names : Nat) (ds : List Nat) :=
  decide (k ≤ ws.toFinset.card) && ds.all (colorRule ws T names) && (colorSet ds == zero)
theorem color_sound {ws T k names ds} (h : colorCheck ws T k names ds=true) :
    Impossible false T k ws.toFinset := by
  simp only [colorCheck,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
  intro n le run
  obtain ⟨F⟩ := oneShare run (le.trans h.1.1)
  have ok := color_set F ds h.1.2
  rw [h.2,bit_zero] at ok
  contradiction
def colorRange (g : Forest) (k a n : Nat) (ds : Nat → Nat × List Nat) :=
  (List.range n).all fun i =>
    colorCheck (stateSet g k (a+i)) (targetOf g) k (ds i).1 (ds i).2
theorem colorCut {g k a n ds} (mode : g.mode=false)
    (h : colorRange g k a n ds=true) : CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have eq : a+(j-a)=j := by omega
  change colorCheck (stateSet g k (a+(j-a))) _ _ _ _=true at hh
  rw [eq] at hh
  exact color_sound hh
def neighbor670 (i : Fin 11) : Nat := [5,8,7,6,5,0,3,2,1,0,0].getD i.val 0
def absentRow670 (i : Fin 11) : Row := Fin.ofNat 2048 (1 <<< neighbor670 i)
def presentRow670 (i : Fin 11) : Row := Fin.ofNat 2048 ((1 <<< i.val) ||| (1 <<< neighbor670 i))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem requiredInputs :
    (∀ i : Fin 11, bit (absentRow670 i) graph ≠ bit (presentRow670 i) graph) ∧
    (∀ i j : Fin 11, i ≠ j →
      bit (absentRow670 i) (inputs.getD j.val zero) =
      bit (presentRow670 i) (inputs.getD j.val zero)) := by decide +kernel
theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 11 C = edge) (small : C.size ≤ 17) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 16 else 17) ∧ Live u graph k inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have len : C.gates.length ≤ 17 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 16 else 17) := by
    by_cases hn : ∀ g ∈ C.gates, isNot g=false
    · refine ⟨false,fun _ => hn,?_⟩
      have := List.countP_le_length (p:=fun g => !isNot g) (l:=C.gates)
      simp only [Bool.false_eq_true,ite_false]
      omega
    · refine ⟨true,by simp,?_⟩
      push Not at hn
      obtain ⟨g,hg,hx⟩ := hn
      have lt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
        rcases Nat.lt_or_ge (C.gates.countP (fun g => !isNot g)) C.gates.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq
          exact absurd eq hx
      simp only [ite_true]
      omega
  obtain ⟨u,mono,count⟩ := mode
  have out := get_rep (u:=u) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates inputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : inputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 11, inputs.getD i.val zero = a := by
    rw [←input_list] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow670 i) (presentRow670 i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩
theorem directSplit
    (m : ∀ k, k ≤ 17 → ¬Live false graph k inputs.toFinset)
    (s : ∀ k, k ≤ 16 → ¬Live true graph k inputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 11 edge 17 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run
def orderLaw (S : Finset Sig) (T : Sig) (f : Sig → Nat) :=
  (∀ {a b p n na nb pa pb}, a ≠ b →
    onlyWire S T a p na → onlyWire S T b p nb →
    onlyWire S T a pa n → onlyWire S T b pb n → f a ≠ f b) ∧
  (∀ {a b c p n na pb}, onlyWire S T a p na → onlyWire S T b pb n →
    onlyWire S T c p n → f a = f b → f c ≤ f a)
theorem only_value {k S T v p n} (run : Live false T k S) (h : onlyWire S T v p n) :
    v∈S ∧ bit p v=true ∧ bit n v=false := by
  obtain ⟨w,hw,hp,hn⟩ := mono_row_difference run rfl h.1 h.2.1
  exact h.2.2 w hw hp hn ▸ ⟨hw,hp,hn⟩
def gateList (a b : Sig) (U : Finset Sig) := [a,b].filter fun t => decide (t∈U)
def gateMap (a b z v : Sig) := if v=a ∨ v=b then z else v
def gateColor (a b z : Sig) (U : Finset Sig) (f : Sig → Nat) (v : Sig) :=
  let kept := gateList a b U
  if v∈kept then kept.idxOf v else kept.length+f (gateMap a b z v)
theorem gate_kept {a b v U} :
    v∈gateList a b U ↔ (v=a ∨ v=b) ∧ v∈U := by simp [gateList]
theorem gate_mem {a b z v : Sig} {U : Finset Sig} (h : v∈insert a (insert b U)) :
    gateMap a b z v ∈ insert z U := by
  by_cases eq : v=a ∨ v=b
  · simp [gateMap,eq]
  · simp_all [gateMap]
theorem mono_bin_bit {d} (hd : allowed false d) (a b : Sig) (r : Row) :
    bit r (bin d a b) = if d=0 then bit r a && bit r b else bit r a || bit r b := by
  rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
  · simp [bit,bin]
  · simp [bit,bin]
  · contradiction
  · contradiction
theorem gate_only {a b d U T v p n} (hd : allowed false d)
    (unused : v∉gateList a b U) (h : onlyWire (insert a (insert b U)) T v p n) :
    onlyWire (insert (bin d a b) U) T (gateMap a b (bin d a b) v) p n := by
  refine ⟨h.1,h.2.1,?_⟩
  intro w hw hp hn
  rcases Finset.mem_insert.mp hw with rfl | hw
  · rw [mono_bin_bit hd] at hp hn
    have sep : (bit p a=true ∧ bit n a=false) ∨ (bit p b=true ∧ bit n b=false) := by
      by_cases op : d=0 <;> cases u : bit p a <;> cases v : bit n a <;> cases x : bit p b <;>
        cases y : bit n b <;> simp_all
    have eq : v=a ∨ v=b := by
      rcases sep with ⟨x,y⟩ | ⟨x,y⟩
      · exact Or.inl (h.2.2 a (by simp) x y).symm
      · exact Or.inr (h.2.2 b (by simp) x y).symm
    simp [gateMap,eq]
  · obtain rfl := h.2.2 w (by simp [hw]) hp hn
    have ne : ¬(w=a ∨ w=b) := fun eq => unused (gate_kept.mpr ⟨eq,hw⟩)
    simp [gateMap,ne]
theorem gate_share_eq {a b z U f v w} (hv : v∈gateList a b U)
    (eq : gateColor a b z U f v = gateColor a b z U f w) : v=w := by
  have bound := List.idxOf_lt_length_of_mem hv
  by_cases hw : w∈gateList a b U
  · simp only [gateColor,if_pos hv,if_pos hw] at eq
    exact (List.idxOf_inj hv).mp eq
  · simp only [gateColor,if_pos hv,if_neg hw] at eq
    omega
theorem gate_cross {a b d U T k p n na nb pa pb} (hd : allowed false d) (hab : a≠b)
    (run : Live false T k (insert (bin d a b) U)) (prev : Live false T (k+1) (insert a (insert b U)))
    (ua : a∉gateList a b U)
    (A : onlyWire (insert a (insert b U)) T a p na) (B : onlyWire (insert a (insert b U)) T b p nb)
    (C : onlyWire (insert a (insert b U)) T a pa n) (D : onlyWire (insert a (insert b U)) T b pb n) : False := by
  have Zp := (only_value run (gate_only hd ua C)).2.1
  have Zn := (only_value run (gate_only hd ua A)).2.2
  simp only [gateMap,true_or,ite_true,mono_bin_bit hd] at Zp Zn
  by_cases op : d=0
  · simp [op] at Zp
    exact hab (C.2.2 b (by simp) Zp.2 (only_value prev D).2.2).symm
  · simp [op] at Zn
    exact hab (A.2.2 b (by simp) (only_value prev B).2.1 Zn.2).symm
theorem order_live {k S T} (h : Live false T k S) :
    ∃ (count : Nat) (f : Sig → Nat), count+S.card ≤ k+2 ∧ (∀ v∈S, f v<count) ∧ orderLaw S T f := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,properT⟩ := h
    refine ⟨1,fun _ => 0,by simp,by simp,?_,by simp⟩
    intro a b p n na nb pa pb ne A B C D
    have e := (only_value (Live.stop (u:=false) properT) A).1
    have j := (only_value (Live.stop (u:=false) properT) B).1
    simp only [Finset.mem_singleton] at e j
    exact (ne (e.trans j.symm)).elim
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,fresh,tail⟩ := h
    let z := bin d a b
    let kept := gateList a b U
    have prev := Live.binary hd ha hb hab fresh tail
    obtain ⟨count,f,mass,bound,law⟩ := ih tail
    have hzu : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem hzu] at mass
    have size : kept.length + (insert a (insert b U)).card = U.card+2 := by
      by_cases x : a∈U <;> by_cases y : b∈U <;>
        simp [kept,gateList,x,y,hab,Finset.card_insert_of_notMem] <;> omega
    refine ⟨kept.length+count,gateColor a b z U f,by omega,?_,?_,?_⟩
    · intro v hv
      by_cases u : v∈kept
      · have m := List.idxOf_lt_length_of_mem u
        change (if v∈kept then kept.idxOf v else _) < _
        rw [if_pos u]
        omega
      · have m := bound _ (gate_mem (z:=z) hv)
        change (if v∈kept then kept.idxOf v else _) < _
        rw [if_neg u]
        exact Nat.add_lt_add_left m _
    · intro v w p n na nb pa pb vw A B C D eq
      have uv : v∉kept := fun u => vw (gate_share_eq u eq)
      have uw : w∉kept := fun u => vw (gate_share_eq u eq.symm).symm
      have same : f (gateMap a b z v) = f (gateMap a b z w) := by
        change (if v∈kept then _ else kept.length+_) = (if w∈kept then _ else kept.length+_) at eq
        rw [if_neg uv,if_neg uw] at eq
        omega
      by_cases ne : gateMap a b z v ≠ gateMap a b z w
      · exact law.1 ne (gate_only hd uv A) (gate_only hd uw B)
          (gate_only hd uv C) (gate_only hd uw D) same
      · have vS := (only_value prev A).1
        have wS := (only_value prev B).1
        have vz : v≠z := fun e => fresh (show z∈_ from e ▸ vS)
        have wz : w≠z := fun e => fresh (show z∈_ from e ▸ wS)
        have pair : (v=a ∧ w=b) ∨ (v=b ∧ w=a) := by
          by_cases va : v=a ∨ v=b <;> by_cases wa : w=a ∨ w=b <;> simp_all [gateMap] <;> grind
        rcases pair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact gate_cross hd hab tail prev uv A B C D
        · exact gate_cross hd hab tail prev uw B A D C
    · intro v w t p n na pb A B C eq
      have ident (e : v=w) : t=v := by
        subst w
        exact (C.2.2 v (only_value prev A).1 (only_value prev A).2.1 (only_value prev B).2.2).symm
      by_cases uv : v∈kept
      · rw [ident (gate_share_eq uv eq)]
      by_cases uw : w∈kept
      · rw [ident (gate_share_eq uw eq.symm).symm]
      have same : f (gateMap a b z v) = f (gateMap a b z w) := by
        change (if v∈kept then _ else kept.length+_) = (if w∈kept then _ else kept.length+_) at eq
        rw [if_neg uv,if_neg uw] at eq
        omega
      change (if t∈kept then kept.idxOf t else kept.length+_) ≤ (if v∈kept then _ else kept.length+_)
      rw [if_neg uv]
      by_cases ut : t∈kept
      · rw [if_pos ut]
        have lim := List.idxOf_lt_length_of_mem ut
        omega
      · rw [if_neg ut]
        exact Nat.add_le_add_left (law.2 (gate_only hd uv A) (gate_only hd uw B) (gate_only hd ut C) same) _
def rankRule (d : Nat) (f : Fin 11 → Nat) : Prop :=
  let v := fun j => f (colorField d j)
  if d.testBit 0 then v 0 ≠ v 1 else v 0=v 1 → v 2≤v 0
theorem rank_rule {ws T names d f} (h : colorRule ws T names d=true)
    (law : orderLaw ws.toFinset T f) :
    rankRule d (fun i => f (colorWire ws names i)) := by
  by_cases flag : d.testBit 0=true
  · simp only [rankRule,colorRule,flag,ite_true,Bool.and_eq_true,decide_eq_true_eq] at h ⊢
    exact law.1 h.1.2 (kwWireB_sound h.2.1.1.1) (kwWireB_sound h.2.1.1.2)
      (kwWireB_sound h.2.1.2) (kwWireB_sound h.2.2)
  · simp only [rankRule,colorRule,if_neg flag,Bool.and_eq_true] at h ⊢
    exact law.2 (kwWireB_sound h.1.1) (kwWireB_sound h.1.2) (kwWireB_sound h.2)
def layerCovers (lo : Nat) (f : Fin 11 → Nat) (t : Nat) :=
  ∀ i, f i<t → lo.testBit i.val=true
def layerBits (lo : Nat) (f : Fin 11 → Nat) (t : Nat) (i : Fin 11) :=
  !lo.testBit i.val && decide (f i=t)
def layerRule (lo d : Nat) : Sig :=
  let x := fun j => inputs.getD (colorField d j).val zero
  let pair := neg (prime false (x 0) (x 1))
  if d.testBit 0 then pair else
    if lo.testBit (colorField d 2).val then one else prime true pair (x 2)
theorem layer_rule {lo d f t} (h : rankRule d f) (cov : layerCovers lo f t) :
    bit (colorPoint (layerBits lo f t)) (layerRule lo d)=true := by
  have eval (j) := color_bit (layerBits lo f t) (colorField d j)
  by_cases flag : d.testBit 0=true
  · simp only [rankRule,flag,ite_true] at h
    simp only [layerRule,flag,ite_true,bit_neg,bit_prime,Bool.false_eq_true,ite_false,eval]
    cases x : layerBits lo f t (colorField d 0) <;> cases y : layerBits lo f t (colorField d 1) <;> simp_all
    simp only [layerBits,Bool.and_eq_true,decide_eq_true_eq] at x y
    exact h (x.2.trans y.2.symm)
  · simp only [rankRule,if_neg flag] at h
    simp only [layerRule,if_neg flag]
    by_cases old : lo.testBit (colorField d 2).val=true
    · rw [if_pos old,bit_one]
    · rw [if_neg old]
      simp only [bit_prime,ite_true,bit_neg,Bool.false_eq_true,ite_false,eval]
      cases x : layerBits lo f t (colorField d 0) <;> cases y : layerBits lo f t (colorField d 1) <;> simp_all
      simp only [layerBits,Bool.and_eq_true,decide_eq_true_eq] at x y
      have le := h (x.2.trans y.2.symm)
      have ge : ¬ f (colorField d 2)<t := by
        intro lt
        have hit := cov _ lt
        simp [old] at hit
      simp [layerBits,old,show f (colorField d 2)=t by omega]
def layerWords (lo : Nat) : List Nat → Sig
  | [] => one
  | d::ds => prime false (layerRule lo d) (layerWords lo ds)
theorem layer_words {lo f t} (ds : List Nat) (h : ∀d∈ds, rankRule d f) (cov : layerCovers lo f t) :
    bit (colorPoint (layerBits lo f t)) (layerWords lo ds)=true := by
  induction ds with
  | nil => exact bit_one _
  | cons d ds ih =>
    rw [layerWords,bit_prime,layer_rule (h d (by simp)) cov,ih (fun e he => h e (by simp [he]))]
    rfl
def cubeParts (mask : Nat) : List (Fin 11) → Sig
  | [] => one
  | i::is => if mask.testBit i.val then cubeParts mask is else
      prime false (neg (inputs.getD i.val zero)) (cubeParts mask is)
theorem cube_parts {x : Fin 11 → Bool} (mask : Nat) (is : List (Fin 11))
    (h : bit (colorPoint x) (cubeParts mask is)=true) :
    ∀ i∈is, x i=true → mask.testBit i.val=true := by
  induction is with
  | nil => simp
  | cons j js ih =>
    by_cases hm : mask.testBit j.val=true
    · rw [cubeParts,if_pos hm] at h
      intro i hi hx
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hm
      · exact ih h i hi hx
    · rw [cubeParts,if_neg hm,bit_prime,bit_neg,color_bit] at h
      simp only [Bool.false_eq_true,ite_false,Bool.and_eq_true,Bool.not_eq_true'] at h
      intro i hi hx
      rcases List.mem_cons.mp hi with rfl | hi
      · simp_all
      · exact ih h.2 i hi hx
def cubeWord (mask : Nat) := cubeParts mask (List.finRange 11)
def layerUpper (lo : Nat) : List Nat → Sig
  | [] => zero
  | a::as => if lo &&& a = lo then prime true (cubeWord a) (layerUpper lo as) else layerUpper lo as
theorem upper_choice {lo f t} (as : List Nat) (cov : layerCovers lo f t)
    (ok : bit (colorPoint (layerBits lo f t)) (layerUpper lo as)=true) :
    ∃ a∈as, layerCovers a f (t+1) := by
  induction as with
  | nil => rw [layerUpper,bit_zero] at ok; contradiction
  | cons a as ih =>
    have follow (h : bit (colorPoint (layerBits lo f t)) (layerUpper lo as)=true) : ∃ v∈a::as, layerCovers v f (t+1) := by
      obtain ⟨v,hv,cv⟩ := ih h
      exact ⟨v,List.mem_cons_of_mem _ hv,cv⟩
    by_cases sub : lo &&& a=lo
    · rw [layerUpper,if_pos sub,bit_prime] at ok
      rcases Bool.or_eq_true_iff.mp ok with hit | tail
      · refine ⟨a,by simp,?_⟩
        intro i hi
        by_cases old : lo.testBit i.val=true
        · have z := congrArg (fun v : Nat => v.testBit i.val) sub
          simpa only [Nat.testBit_and,old,Bool.true_and] using z
        · have ge : ¬ f i<t := fun lt => old (cov i lt)
          have yes : layerBits lo f t i=true := by simp [layerBits,old,show f i=t by omega]
          exact cube_parts a (List.finRange 11) hit i (by simp) yes
      · exact follow tail
    · rw [layerUpper,if_neg sub] at ok
      exact follow ok
def layerStep (ds : List Nat) (lo : Nat) (hi : List Nat) :=
  (prime false (layerWords lo ds) (neg (layerUpper lo hi)) == zero)
theorem layer_step {ds lo hi f t} (laws : ∀d∈ds,rankRule d f) (cov : layerCovers lo f t)
    (ok : layerStep ds lo hi=true) : ∃ a∈hi, layerCovers a f (t+1) := by
  have eq := beq_iff_eq.mp ok
  have chk := congrArg (bit (colorPoint (layerBits lo f t))) eq
  rw [bit_prime,bit_neg,bit_zero,layer_words ds laws cov] at chk
  apply upper_choice hi cov
  simpa using chk
def finalPair (lo d : Nat) := d.testBit 0 && !lo.testBit (colorField d 0).val && !lo.testBit (colorField d 1).val
def layerScan (ds lo : List Nat) : List (List Nat) → Bool
  | [] => lo.all fun a => ds.any (finalPair a)
  | hi::tail => (lo.all fun a => layerStep ds a hi) && layerScan ds hi tail
theorem layer_scan {ds f} (laws : ∀d∈ds,rankRule d f) (ls : List (List Nat))
    {lo t} (covered : ∃a∈lo,layerCovers a f t) (bound : ∀i, f i<t+ls.length+1)
    (ok : layerScan ds lo ls=true) : False := by
  induction ls generalizing lo t with
  | nil =>
    obtain ⟨a,ha,ca⟩ := covered
    obtain ⟨d,hd,yes⟩ := List.any_eq_true.mp (List.all_eq_true.mp ok a ha)
    simp only [finalPair,Bool.and_eq_true,Bool.not_eq_true'] at yes
    have top (i : Fin 11) (no : a.testBit i.val=false) : f i=t := by
      have small : f i<t+1 := by simpa using bound i
      have big : ¬ f i<t := by intro lt; have hh := ca i lt; simp [no] at hh
      omega
    have diff := laws d hd
    simp only [rankRule,yes.1.1,ite_true] at diff
    exact diff ((top _ yes.1.2).trans (top _ yes.2).symm)
  | cons l ls ih =>
    obtain ⟨a,ha,ca⟩ := covered
    have both := Bool.and_eq_true_iff.mp ok
    apply ih (t:=t+1) (layer_step laws ca (List.all_eq_true.mp both.1 a ha)) _ both.2
    intro i
    have z := bound i
    simp only [List.length_cons] at z
    omega
abbrev OrderPage := Nat × List Nat × Nat × List (List Nat)
def orderCheck (ws : List Sig) (T : Sig) (k : Nat) (book : OrderPage) :=
  let (names,ds,start,ls) := book
  decide (k+2 ≤ ws.toFinset.card+ls.length+1) &&
    (List.finRange 11).all (fun i => decide (colorWire ws names i ∈ ws)) &&
    ds.all (colorRule ws T names) && layerScan ds [start] ls
theorem order_sound {ws T k page} (ok : orderCheck ws T k page=true) : Impossible false T k ws.toFinset := by
  rcases page with ⟨names,ds,start,ls⟩
  simp only [orderCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at ok
  intro n le run
  obtain ⟨count,f,mass,bound,law⟩ := order_live run
  apply layer_scan (f:=fun i => f (colorWire ws names i)) (fun d hd => rank_rule (ok.1.2 d hd) law)
    ls (t:=0) (lo:=[start]) ⟨start,by simp,by simp [layerCovers]⟩ _ ok.2
  intro i
  have use := (ok.1.1.2 _ (List.mem_finRange i))
  have less := bound _ (List.mem_toFinset.mpr use)
  have size := ok.1.1.1
  omega
def orderRange (g : Forest) (k a n : Nat) (pages : Nat → OrderPage) :=
  (List.range n).all fun i => orderCheck (stateSet g k (a+i)) (targetOf g) k (pages i)
theorem orderCut {g k a n pages} (mode : g.mode=false) (ok : orderRange g k a n pages=true) :
    CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp ok (j-a) (List.mem_range.mpr (by omega))
  have eq : a+(j-a)=j := by omega
  change orderCheck (stateSet g k (a+(j-a))) _ _ _=true at hh
  rw [eq] at hh
  exact order_sound hh
def padColumn (n v : Nat) : Bits :=
  BitVec.ofNat 320 (v + if v % 2=1 then (1 <<< 320)-(1 <<< n) else 0)
theorem lowerHint {u raw T a b} (h : Lower u raw T a) (le : b ≤ a) : Lower u raw T b :=
  fun p bank hr hit => le.trans (h p bank hr hit)
def treeData (p n v : Nat) :=
  let row := fun base i => (base >>> (11*((v >>> (8+5*i)) % 32))) % 2048
  v % 256 + (row p 0 <<< 8) + (row n 1 <<< 19) + (row n 2 <<< 30) +
    (row n 3 <<< 41) + (row p 4 <<< 52) + (row p 5 <<< 63)
def ruleData (p n v : Nat) :=
  let row := fun base i => (base >>> (11*((v >>> (13+5*i)) % 32))) % 2048
  v % 8192 + (row p 0 <<< 13) + (row n 1 <<< 24) + (row n 2 <<< 35) +
    (row (if v.testBit 0 then n else p) 3 <<< 46) + (row p 4 <<< 57) + (row p 5 <<< 68)
theorem countFace {u m L} (hints : Nat)
    (hp : properB (graphGoal m)=true)
    (ess : checkEssential (graphGoal m) (varsX m) (graphPairs m hints)=true)
    (enough : L ≤ (List.map Prod.fst (graphPairs m hints)).toFinset.card - 1) :
    Lower u (varsX m) (graphGoal m) L :=
  lowerHint (lower_count (proper_of _ hp) (graphPairs m hints) ess) enough
theorem dropFace {u m q a L} (fixed hints : Nat) (prior : Lower u (varsX q) (graphGoal q) a)
    (mapped : checkLift (fixRows fixed 0) (graphGoal m) (varsX m) (varsX q) (graphGoal q) (graphPairs fixed hints)=true)
    (hm : properB (graphGoal m)=true) (hq : properB (graphGoal q)=true)
    (enough : L ≤ a + (List.map Prod.fst (graphPairs fixed hints)).toFinset.card) :
    Lower u (varsX m) (graphGoal m) L :=
  lowerHint (lift_ok mapped (proper_of _ hm) (proper_of _ hq) prior) enough
abbrev Face (u : Bool) (m L : Nat) := Lower u (varsX m) (graphGoal m) L
def tableWord (xs : Array Nat) (i : Nat) := xs.getD (i%8) 0
def tablePair (xs : Array (Nat × Nat)) (i : Nat) := xs.getD (i%8) (0,0)
def tableBits (xs : Array (Bits × Bits)) (i : Nat) := xs.getD (i%8) (0,0)
def readRules (pos neg width : Nat) (rules : Nat → Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,v => ruleData pos neg (rules (v % (1 <<< width))) :: readRules pos neg width rules n (v >>> width)
def readPanel (pos neg rw pw : Nat) (rules programs : Nat → Nat) (rec : Nat) :=
  let program := programs (rec % (1 <<< pw))
  (rec >>> pw,readRules pos neg rw rules (program % 16) (program >>> 4))
theorem consFace {u m L es} (h : Face u m L) (tail : Known u es) : Known u ((m,L)::es) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | h'
  · exact h
  · exact tail e h'
def smallSlot (h buckets slots iw pw : Nat) (disp slotsAt : Nat → Nat) : Option (Nat × Nat) :=
  let slot := (h/buckets+disp (h%buckets))%slots
  let val := slotsAt slot
  if val=0 || (val >>> (iw+pw)) != (h/(buckets*slots))%8 then none
  else some (val % (1 <<< iw)-1,(val >>> iw)%(1 <<< pw))
def variableSlot (blocks : Nat → Nat × Nat) (i : Nat) :=
  let b := blocks (i/16)
  let offsets := b.1 >>> (12*(i%16))
  let start := offsets % 4096
  (b.2 >>> start) % (1 <<< ((offsets >>> 12)%4096 - start))
def bookData (d fw mw : Nat) (fronts masks codes costs : Nat → Nat) (j : Nat) :=
  let i := j/2
  if j%2=1 then costs i else
    let code := codes i
    fronts (code % (1 <<< fw)) + ((code >>> (fw+mw)) <<< (12*(d-1))) +
      (masks ((code >>> fw)%(1 <<< mw)) <<< (12*d))
noncomputable def bandTest (g : Forest) (k a n ar : Nat) :=
  header g k a n ar && rowCut g k a n ar 0 ar
theorem bandTest_sound {g k a n ar} (ok : bandTest g k a n ar=true) :
    block g k a n=true :=
  cutsBlock (Bool.and_eq_true_iff.mp ok).1 (Bool.and_eq_true_iff.mp ok).2
noncomputable def bandCells (g : Forest) (k a n ar : Nat) (splitBand : Bool) :=
  if splitBand then bandTest g k a (n/2) ar && bandTest g k (a+n/2) (n-n/2) ar
  else bandTest g k a n ar
theorem bandCut {g k a n} (ar : Nat) (splitBand : Bool) (ok : bandCells g k a n ar splitBand=true) :
    CutRow g k a n := by
  apply checkedRow
  cases splitBand
  · exact bandTest_sound ok
  · have both := Bool.and_eq_true_iff.mp ok
    have all := block_merge (bandTest_sound both.1) (bandTest_sound both.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using all
def readGroup (n pad : Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | s+1,x => (pad+x % (1 <<< n)) :: readGroup n pad s (x >>> n)
def readGroups (n pad : Nat) : Nat → Nat → List (List Nat)
  | 0,_ => []
  | s+1,x =>
    let len := x % 64
    readGroup n pad len (x >>> 6) :: readGroups n pad s (x >>> (6+n*len))
def orderPage (pos neg w : Nat) (bank : Nat → Nat) (n q names clauses groups : Nat) : OrderPage :=
  let pad := 2048-(1 <<< n)
  (names,readRules pos neg w bank (clauses % 128) (clauses >>> 7),pad,readGroups n pad (q-1) groups)

namespace B209_4
def entries : List (Nat × Nat) := []
theorem prior : Known true entries := known_down baseKnown
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 10 0x1f,padColumn 10 0x20a),(padColumn 10 0x0,padColumn 10 0x0),(padColumn 10 0x0,padColumn 10 0x0),(padColumn 10 0x0,padColumn 10 0x0),(padColumn 10 0x3e0,padColumn 10 0x120),(padColumn 10 0x7f,padColumn 10 0x54),(padColumn 10 0x380,padColumn 10 0x218),(padColumn 10 0x0,padColumn 10 0x0)] i else tableBits #[(padColumn 10 0x0,padColumn 10 0x0),(padColumn 10 0x0,padColumn 10 0x0),(padColumn 10 0x0,padColumn 10 0x0)] i))
def cols : List ColumnInfo := []
def data3 : Nat → Nat := (fun i => tableWord #[0xf,0x0] i)
def levels : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,data3)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def book : Forest := ⟨113,3,samples,cols,[[],[96,84]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row3_0 : CutRow book 3 0 1 := bandCut 4 false (by decide +kernel)
theorem band3 : CutRow book 3 0 1 := row3_0
theorem checked : mixedTables book 3 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band3
end B209_4
theorem h209_4 : Face true 113 4 :=
  mixedLower (g:=B209_4.book) (i:=0) (hints:=67436549)
    (before_sound B209_4.entries B209_4.prior) B209_4.geometry B209_4.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h216_4 : Face true 120 4 := carry_of (swaps:=[101,48,32,16]) (by decide +kernel) h209_4
theorem h408_4 : Face true 216 4 := carry_of (swaps:=[101,117,64,48,32,16]) (by decide +kernel) h209_4

namespace B473_7
def entries : List (Nat × Nat) := [(120,4),(113,4),(216,4)]
theorem prior : Known true entries := (consFace h216_4 (consFace h209_4 (consFace h408_4 (known_down baseKnown))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 36 0x191c603ff,padColumn 36 0x90d60153),(padColumn 36 0x0,padColumn 36 0x0),(padColumn 36 0x0,padColumn 36 0x0),(padColumn 36 0x27e07c300,padColumn 36 0x23a02d30a),(padColumn 36 0xc60787c00,padColumn 36 0x860280400),(padColumn 36 0x787807fff,padColumn 36 0x707007aac),(padColumn 36 0x807ff8000,padColumn 36 0x5d50030),(padColumn 36 0xff8000000,padColumn 36 0xdc02020c0)] i else tableBits #[(padColumn 36 0x0,padColumn 36 0x0),(padColumn 36 0x0,padColumn 36 0x0),(padColumn 36 0x0,padColumn 36 0x0)] i))
def cols : List ColumnInfo := [(129,0,120,0,4),(0,128,113,8,5),(0,1,216,32,5)]
def data6 : Nat → Nat := (fun i => tableWord #[0x3f,0x1803] i)
def levels : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,data6)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def book : Forest := ⟨249,6,samples,cols,[[],[112,83,100]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 1 := bandCut 6 false (by decide +kernel)
theorem band6 : CutRow book 6 0 1 := row6_0
theorem checked : mixedTables book 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band6
end B473_7
theorem h473_7 : Face true 249 7 :=
  mixedLower (g:=B473_7.book) (i:=0) (hints:=855990277)
    (before_sound B473_7.entries B473_7.prior) B473_7.geometry B473_7.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h476_7 : Face true 252 7 := carry_of (swaps:=[117,67,32,16]) (by decide +kernel) h473_7
theorem h594_4 : Face true 306 4 := carry_of (swaps:=[133,117,101,16]) (by decide +kernel) h209_4
theorem h658_4 : Face true 338 4 := carry_of (swaps:=[133,117,16]) (by decide +kernel) h209_4
theorem h598_5 : Face true 310 5 := dropFace 4 4299491456 h594_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h721_5 : Face true 369 5 := carry_of (swaps:=[65,132,98,50,16,80]) (by decide +kernel) h598_5

namespace B723_7
def entries : List (Nat × Nat) := [(113,4),(306,4),(338,4),(369,5)]
theorem prior : Known true entries := (consFace h209_4 (consFace h594_4 (consFace h658_4 (consFace h721_5 (known_down baseKnown)))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 37 0x198d803ff,padColumn 37 0x985c0153),(padColumn 37 0x1e1f202300,padColumn 37 0xa0b22b30a),(padColumn 37 0x0,padColumn 37 0x0),(padColumn 37 0x0,padColumn 37 0x0),(padColumn 37 0x603ffc00,padColumn 37 0x202b0400),(padColumn 37 0x780c03fff,padColumn 37 0x700803aac),(padColumn 37 0x1800ffc000,padColumn 37 0x1802d40030),(padColumn 37 0x0,padColumn 37 0x0)] i else tableBits #[(padColumn 37 0x1fff000000,padColumn 37 0x15d40000c0),(padColumn 37 0x0,padColumn 37 0x0),(padColumn 37 0x0,padColumn 37 0x0)] i))
def cols : List ColumnInfo := [(256,2,113,0,4),(65,0,306,0,4),(32,1,338,0,4),(2,0,369,0,5)]
def data6 : Nat → Nat := (fun i => tableWord #[0x3f,0xd204] i)
def data5 : Nat → Nat := (fun i => tableWord #[0x6f882,0x0] i)
def levels : Nat → Packing
  | 5 => (1,1,2,0,0,0,0,data5)
  | 6 => (1,0,2,0,0,0,0,data6)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun v => (if v=5342971937700010185 then some (0,0) else none)
  | _ => fun _ => none
def book : Forest := ⟨371,6,samples,cols,[[],[16,133]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 1 := bandCut 6 false (by decide +kernel)
theorem band6 : CutRow book 6 0 1 := row6_0
set_option maxRecDepth 16000 in
theorem row5_0 : CutRow book 5 0 1 := bandCut 6 false (by decide +kernel)
theorem band5 : CutRow book 5 0 1 := row5_0
theorem checked : mixedTables book 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band5
  · exact band6
end B723_7
theorem h723_7 : Face true 371 7 :=
  mixedLower (g:=B723_7.book) (i:=0) (hints:=4362403973)
    (before_sound B723_7.entries B723_7.prior) B723_7.geometry B723_7.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h730_7 : Face true 378 7 := carry_of (swaps:=[101,48,32]) (by decide +kernel) h723_7
theorem h854_7 : Face true 438 7 := carry_of (swaps:=[112,16,132,80,97,32]) (by decide +kernel) h723_7
theorem h910_7 : Face true 462 7 := carry_of (swaps:=[118,133,66,16]) (by decide +kernel) h473_7
theorem h918_7 : Face true 470 7 := carry_of (swaps:=[112,132,80,97,32]) (by decide +kernel) h723_7
theorem h922_7 : Face true 474 7 := carry_of (swaps:=[133,16]) (by decide +kernel) h473_7
theorem h396_4 : Face true 204 4 := carry_of (swaps:=[117,67,32,16]) (by decide +kernel) h209_4
theorem h660_4 : Face true 340 4 := carry_of (swaps:=[133,117,32,16]) (by decide +kernel) h209_4
theorem h664_4 : Face true 344 4 := carry_of (swaps:=[134,101,117,48,32,16]) (by decide +kernel) h209_4
theorem h217_5 : Face true 121 5 := dropFace 8 50683909 h209_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h668_5 : Face true 348 5 := carry_of (swaps:=[133,117,32,16]) (by decide +kernel) h217_5
theorem h780_4 : Face true 396 4 := carry_of (swaps:=[134,117,48,64,32,16]) (by decide +kernel) h209_4
theorem h788_4 : Face true 404 4 := carry_of (swaps:=[101,134,117,64,32,16]) (by decide +kernel) h209_4

namespace B924_8
def entries : List (Nat × Nat) := [(204,4),(216,4),(340,4),(344,4),(348,5),(396,4),(404,4)]
theorem prior : Known true entries := (consFace h396_4 (consFace h408_4 (consFace h660_4 (consFace h664_4 (consFace h668_5 (consFace h780_4 (consFace h788_4 (known_down baseKnown))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 38 0x0,padColumn 38 0x0),(padColumn 38 0x0,padColumn 38 0x0),(padColumn 38 0x27cd8f860,padColumn 38 0x23c48786a),(padColumn 38 0x1d6027007f,padColumn 38 0x1568050033),(padColumn 38 0x2183381f80,padColumn 38 0x2081380a80),(padColumn 38 0x0,padColumn 38 0x0),(padColumn 38 0xe03c01fff,padColumn 38 0xa12c0554c),(padColumn 38 0x3003ffe000,padColumn 38 0x2003b28600)] i else tableBits #[(padColumn 38 0x3ffc000000,padColumn 38 0x1d40040010),(padColumn 38 0x0,padColumn 38 0x0),(padColumn 38 0x0,padColumn 38 0x0)] i))
def cols : List ColumnInfo := [(272,0,204,0,4),(260,0,216,0,4),(136,0,340,0,4),(132,0,344,0,4),(128,0,348,0,5),(80,0,396,0,4),(72,0,404,0,4)]
def data7 : Nat → Nat := (fun i => tableWord #[0x3f,0xd43306] i)
def data6 : Nat → Nat := (fun i => tableWord #[0x7f420,0x401,0x7f460,0x0] i)
def data5 : Nat → Nat := (fun i => tableWord #[0xaf886420,0x0] i)
def levels : Nat → Packing
  | 5 => (1,2,3,0,0,0,0,data5)
  | 6 => (2,1,3,0,0,0,0,data6)
  | 7 => (1,0,3,0,0,0,0,data7)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun v => (if v=5688551321472505468 then some (0,0) else none)
  | 7 => fun h => smallSlot h 3 13 2 4 (fun i => (((fun i => tableWord #[0x7] i)) (i/16) >>> (3*(i%16))) % 8) (fun i => (((fun i => tableWord #[0x40800a5d9a6896ba00610018b4a] i)) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨476,7,samples,cols,[[],[67,135],[50,134],[50,66,134,118],[66,50,118,134],[66,118],[98,115,132],[98,131,116],[114,99,132,67,50],[114,131,100],[130,99,116],[130,115,100,67,66]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row7_0 : CutRow book 7 0 1 := bandCut 6 false (by decide +kernel)
theorem band7 : CutRow book 7 0 1 := row7_0
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 2 := bandCut 7 false (by decide +kernel)
theorem band6 : CutRow book 6 0 2 := row6_0
set_option maxRecDepth 16000 in
theorem row5_0 : CutRow book 5 0 1 := bandCut 6 false (by decide +kernel)
theorem band5 : CutRow book 5 0 1 := row5_0
theorem checked : mixedTables book 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band5
  · exact band6
  · exact band7
end B924_8
theorem h924_8 : Face true 476 8 :=
  mixedLower (g:=B924_8.book) (i:=0) (hints:=9177556736)
    (before_sound B924_8.entries B924_8.prior) B924_8.geometry B924_8.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h727_8 : Face true 375 8 := dropFace 4 4362406021 h723_7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h982_8 : Face true 502 8 := carry_of (swaps:=[33,132,112,82,97,48]) (by decide +kernel) h727_8
theorem h596_4 : Face true 308 4 := carry_of (swaps:=[133,117,101,32,16]) (by decide +kernel) h209_4
theorem h774_4 : Face true 390 4 := carry_of (swaps:=[101,134,117,50,66,16]) (by decide +kernel) h209_4
theorem h860_7 : Face true 444 7 := carry_of (swaps:=[132,64,84,115,96,32,16]) (by decide +kernel) h473_7

namespace B990_11
def entries : List (Nat × Nat) := [(120,4),(204,4),(216,4),(252,7),(306,4),(308,4),(338,4),(378,7),(390,4),(438,7),(444,7),(462,7),(470,7),(474,7),(476,8)]
theorem prior : Known true entries := (consFace h216_4 (consFace h396_4 (consFace h408_4 (consFace h476_7 (consFace h594_4 (consFace h596_4 (consFace h658_4 (consFace h730_7 (consFace h774_4 (consFace h854_7 (consFace h860_7 (consFace h910_7 (consFace h918_7 (consFace h922_7 (consFace h924_8 (known_down baseKnown))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 125 0x0,padColumn 125 0x0),(padColumn 125 0x60618c3e1f800001c40101c0000c00,padColumn 125 0x2020881c45090421c50140c0514c08),(padColumn 125 0x818610c7e00e073e07c60e0003f000,padColumn 125 0x821046a202010a00460f04819012),(padColumn 125 0x70e0060f8001038c3f8180ffffc0000,padColumn 125 0x2060060f840001042a8080651fe6020),(padColumn 125 0x1810187f000061c0fc0027f0001fffff,padColumn 125 0x800003d00004040fc00029000047483),(padColumn 125 0x1f80000001ff00003800001fffff,padColumn 125 0x41780109401bf00001804011b8b7c),(padColumn 125 0x1fe00000007e0000003fffffe00000,padColumn 125 0x19e00000001e0000003469ae000040),(padColumn 125 0x1fe0000000007fffffffc00000000000,padColumn 125 0x1ce0000000007de6b117808008000180)] i else tableBits #[(padColumn 125 0x1fffffffffff80000000000000000000,padColumn 125 0x17df5d42a11800000022000030000200),(padColumn 125 0x0,padColumn 125 0x0),(padColumn 125 0x0,padColumn 125 0x0)] i))
def cols : List ColumnInfo := [(386,4,120,0,4),(384,6,120,0,4),(274,32,204,0,4),(272,34,204,0,4),(294,0,216,0,4),(292,2,216,0,4),(256,6,120,128,5),(256,2,252,0,7),(196,8,306,0,4),(202,0,308,0,4),(194,8,308,0,4),(44,128,338,0,4),(36,128,338,8,5),(132,0,378,0,7),(24,96,390,0,4),(16,96,390,8,5),(68,8,306,128,5),(66,8,308,128,5),(72,0,438,0,7),(66,0,444,0,7),(16,32,462,0,7),(40,0,470,0,7),(36,0,474,0,7),(34,0,476,0,8),(0,34,204,272,6),(0,6,120,384,6),(0,2,252,256,8)]
def data10 : Nat → Nat := (fun i => tableWord #[0xff,0x7a49b705] i)
def data9 : Nat → Nat := (fun i => (if i<8 then tableWord #[0x1fe420,0x3742c858706,0x1fe460,0xf5d9cad50707,0x1fece0,0x674cad5c706,0x1ff441,0x3512c104] i else (if i<16 then tableWord #[0x1ff461,0x1a5ce41650107,0x1ff4a1,0x38102,0x1ff4e1,0x5c700504,0x1ff462,0x4d441538a06] i else tableWord #[0x1ff4c2,0x24b02,0x1ff4e2,0x51740754a06,0x1ff4e3,0xc1875375ce20309] i)))
def data8 : Nat → Nat := (fun i => (if i<16 then (if i<8 then tableWord #[0x3fc441420,0x1a45a8104,0x2fe868420,0x135a0403,0x3ee883420,0x268302,0x3ee4a4420,0x40302] i else tableWord #[0x2fed01460,0x1b0202,0x2fe428ce0,0xc8502,0x2fe468ce0,0x15cc8303,0x3ee883ce0,0x301] i) else (if i<24 then tableWord #[0x2bf8c8441,0x14bb8603,0x2df8a8462,0x43b8f03,0x3fe4a3420,0xbb402,0x3fe4c2460,0x0] i else (if i<32 then tableWord #[0x3fe462ce0,0x4da1703,0x3fe4c2ce0,0x0,0x3fe4a3ce0,0xbb402,0x3fe4c3ce0,0x1a1702] i else tableWord #[0x3fe4c5ce0,0x3501,0x2ffd034e2,0xc1702] i))))
def data7 : Nat → Nat := (fun i => (if i<8 then tableWord #[0x4ee509883ce0,0x0,0x6fc868441420,0x8d01,0x7ec883441420,0x8d01,0x5ee4a9883420,0x0] i else tableWord #[0x6ee883428ce0,0x0,0x5de8a9462ce0,0x0,0x5fad224c5ce0,0x0] i))
def levels : Nat → Packing
  | 7 => (7,3,5,0,0,0,0,data7)
  | 8 => (18,2,5,0,0,0,0,data8)
  | 9 => (11,1,5,0,0,0,0,data9)
  | 10 => (1,0,5,0,0,0,0,data10)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun h => smallSlot h 4 15 3 1 (fun i => (((fun i => tableWord #[0x30] i)) (i/16) >>> (2*(i%16))) % 4) (fun i => (((fun i => tableWord #[0x1580000188e01fb0c06f8f545c4] i)) (i/16) >>> (7*(i%16))) % 128)
  | 9 => fun h => smallSlot h 9 31 5 1 (fun i => (((fun i => tableWord #[0x7600485] i)) (i/16) >>> (3*(i%16))) % 8) (fun i => (((fun i => tableWord #[0x824040000e482ca290005140083000be0f8d,0x18d2431e57395d063853d56ec0020b19c8] i)) (i/16) >>> (9*(i%16))) % 512)
  | 10 => fun h => smallSlot h 7 28 4 1 (fun i => (((fun i => tableWord #[0x2007c] i)) (i/16) >>> (3*(i%16))) % 8) (fun i => (((fun i => tableWord #[0xbc300880000d2000000c70000f85a,0xc9e275b3b1a6776104ea05b4] i)) (i/16) >>> (8*(i%16))) % 256)
  | _ => fun _ => none
def book : Forest := ⟨510,10,samples,cols,[[],[81,98,115,132]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 8 false (by decide +kernel)
theorem band10 : CutRow book 10 0 1 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 3 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row9_3 : CutRow book 9 3 8 := bandCut 9 false (by decide +kernel)
theorem combine9_0_11 : CutRow book 9 0 11 := @joinRow book 9 0 3 8 row9_0 row9_3
theorem band9 : CutRow book 9 0 11 := combine9_0_11
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 10 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_10 : CutRow book 8 10 8 := bandCut 9 false (by decide +kernel)
theorem combine8_0_18 : CutRow book 8 0 18 := @joinRow book 8 0 10 8 row8_0 row8_10
theorem band8 : CutRow book 8 0 18 := combine8_0_18
set_option maxRecDepth 16000 in
theorem row7_0 : CutRow book 7 0 1 := bandCut 7 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_1 : CutRow book 7 1 6 := bandCut 8 false (by decide +kernel)
theorem combine7_0_7 : CutRow book 7 0 7 := @joinRow book 7 0 1 6 row7_0 row7_1
theorem band7 : CutRow book 7 0 7 := combine7_0_7
theorem checked : mixedTables book 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band7
  · exact band8
  · exact band9
  · exact band10
end B990_11
theorem h990_11 : Face true 510 11 :=
  mixedLower (g:=B990_11.book) (i:=0) (hints:=4886718336)
    (before_sound B990_11.entries B990_11.prior) B990_11.geometry B990_11.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1227_7 : Face true 619 7 := carry_of (swaps:=[148,64,65,67,83,97,128]) (by decide +kernel) h723_7
theorem h1235_7 : Face true 627 7 := carry_of (swaps:=[147,131,84,50,33,113,96]) (by decide +kernel) h473_7
theorem h1241_8 : Face true 633 8 := carry_of (swaps:=[151,117,133,16,32]) (by decide +kernel) h924_8
theorem h1242_7 : Face true 634 7 := carry_of (swaps:=[149,133,117,67,16]) (by decide +kernel) h473_7
theorem h1355_7 : Face true 683 7 := carry_of (swaps:=[148,113,67,131,97,80]) (by decide +kernel) h723_7
theorem h1434_7 : Face true 730 7 := carry_of (swaps:=[149,101,134,117,65,49,16,32]) (by decide +kernel) h723_7
theorem h853_7 : Face true 437 7 := carry_of (swaps:=[132,100,50,82,112]) (by decide +kernel) h473_7
theorem h855_8 : Face true 439 8 := dropFace 2 4832167813 h853_7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1498_8 : Face true 762 8 := carry_of (swaps:=[146,66,64,84,128,98,113,48]) (by decide +kernel) h855_8
theorem h1499_11 : Face true 763 11 := carry_of (swaps:=[148,65,49,116,131,32,81,96]) (by decide +kernel) h990_11
theorem h461_6 : Face true 237 6 := dropFace 33 587228933 h396_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h858_6 : Face true 442 6 := carry_of (swaps:=[131,82,114,48,66,96,16]) (by decide +kernel) h461_6
theorem h593_4 : Face true 305 4 := carry_of (swaps:=[134,118]) (by decide +kernel) h209_4
theorem h599_6 : Face true 311 6 := dropFace 6 4295297157 h593_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h984_6 : Face true 504 6 := carry_of (swaps:=[65,32,132,80,114,97,48]) (by decide +kernel) h599_6
theorem h985_8 : Face true 505 8 := carry_of (swaps:=[65,33,132,81,98,49,112]) (by decide +kernel) h855_8

namespace B987_10
def entries : List (Nat × Nat) := [(249,7),(371,7),(378,7),(442,6),(474,7),(504,6),(216,4),(505,8)]
theorem prior : Known true entries := (consFace h473_7 (consFace h723_7 (consFace h730_7 (consFace h858_6 (consFace h922_7 (consFace h984_6 (consFace h408_4 (consFace h985_8 (known_down baseKnown)))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 75 0x30c1881c018007fff,padColumn 75 0x10c0880c418002a87),(padColumn 75 0x33c3f01000060101800,padColumn 75 0x1141501100862921812),(padColumn 75 0x0,padColumn 75 0x0),(padColumn 75 0x4c03027fe007fe06000,padColumn 75 0x4403023da0028e46024),(padColumn 75 0xc0c6007f803f8000,padColumn 75 0x4086001100008000),(padColumn 75 0xf00780780003fffff,padColumn 75 0xe00700700003f5578),(padColumn 75 0xf0008007ffffc00000,padColumn 75 0xb0000005ee57080040),(padColumn 75 0x70000fff80000000000,padColumn 75 0x30000dc203000000180)] i else tableBits #[(padColumn 75 0x7ffff00000000000000,padColumn 75 0x6ebaa00400004000600),(padColumn 75 0x0,padColumn 75 0x0),(padColumn 75 0x0,padColumn 75 0x0)] i))
def cols : List ColumnInfo := [(256,2,249,0,7),(8,128,371,0,7),(129,0,378,0,7),(0,128,371,8,8),(65,0,442,0,6),(32,1,474,0,7),(3,0,504,0,6),(0,3,216,288,6),(2,0,505,0,8)]
def data9 : Nat → Nat := (fun i => tableWord #[0xff,0x84150206] i)
def data8 : Nat → Nat := (fun i => tableWord #[0x1ff4a3,0x0,0x1ff8a3,0x4cc703] i)
def levels : Nat → Packing
  | 8 => (2,1,4,0,0,0,0,data8)
  | 9 => (1,0,4,0,0,0,0,data9)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 9 => fun v => (if v=5983076478365830632 then some (1,0) else (if v=6463100887286636623 then some (0,0) else none))
  | _ => fun _ => none
def book : Forest := ⟨507,9,samples,cols,[[],[16,133]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 1 := bandCut 8 false (by decide +kernel)
theorem band9 : CutRow book 9 0 1 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 2 := bandCut 9 false (by decide +kernel)
theorem band8 : CutRow book 8 0 2 := row8_0
theorem checked : mixedTables book 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band8
  · exact band9
end B987_10
theorem h987_10 : Face true 507 10 :=
  mixedLower (g:=B987_10.book) (i:=0) (hints:=5150957701)
    (before_sound B987_10.entries B987_10.prior) B987_10.geometry B987_10.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1502_10 : Face true 766 10 := carry_of (swaps:=[149,133,117,67,16,32]) (by decide +kernel) h987_10
theorem h1619_8 : Face true 819 8 := carry_of (swaps:=[151,101,133,49,32]) (by decide +kernel) h924_8
theorem h1690_8 : Face true 858 8 := carry_of (swaps:=[118,151,134,66,33,49]) (by decide +kernel) h924_8
theorem h926_9 : Face true 478 9 := dropFace 2 4882589568 h924_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1754_9 : Face true 890 9 := carry_of (swaps:=[50,146,67,33,132,99,82,113]) (by decide +kernel) h926_9
theorem h65_1 : Face true 33 1 := countFace 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h144_1 : Face true 80 1 := carry_of (swaps:=[101,64,48,32,16]) (by decide +kernel) h65_1
theorem h81_2 : Face true 49 2 := countFace 327685 (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h729_7 : Face true 377 7 := carry_of (swaps:=[101,133,48,32,16]) (by decide +kernel) h723_7
theorem h1089_2 : Face true 545 2 := carry_of (swaps:=[144,128,112,64,100,80]) (by decide +kernel) h81_2
theorem h1091_4 : Face true 547 4 := carry_of (swaps:=[149,133,117,101,50,33,16,64]) (by decide +kernel) h209_4
theorem h1097_4 : Face true 553 4 := carry_of (swaps:=[149,133,117,101,48,64]) (by decide +kernel) h209_4
theorem h1161_4 : Face true 585 4 := carry_of (swaps:=[149,133,117,67]) (by decide +kernel) h209_4
theorem h1162_4 : Face true 586 4 := carry_of (swaps:=[149,133,117,67,16]) (by decide +kernel) h209_4
theorem h1176_4 : Face true 600 4 := carry_of (swaps:=[150,134,101,117,64,48,32,16]) (by decide +kernel) h209_4
theorem h1539_4 : Face true 771 4 := carry_of (swaps:=[149,134,117,50,33,65]) (by decide +kernel) h209_4
theorem h1546_4 : Face true 778 4 := carry_of (swaps:=[149,134,117,48,64,16]) (by decide +kernel) h209_4
theorem h514_1 : Face true 258 1 := carry_of (swaps:=[133,117,101,16]) (by decide +kernel) h65_1
theorem h1611_7 : Face true 811 7 := carry_of (swaps:=[148,116,67,99,81,128]) (by decide +kernel) h723_7
theorem h1625_7 : Face true 825 7 := carry_of (swaps:=[117,151,133,101,48,64]) (by decide +kernel) h473_7
theorem h1626_7 : Face true 826 7 := carry_of (swaps:=[149,134,117,48,64,16]) (by decide +kernel) h473_7
theorem h1675_7 : Face true 843 7 := carry_of (swaps:=[64,144,16,113,67,131,81,96]) (by decide +kernel) h723_7

namespace B1755_12
def entries : List (Nat × Nat) := [(33,1),(80,1),(113,4),(120,4),(305,4),(49,2),(306,4),(338,4),(344,4),(371,7),(377,7),(378,7),(545,2),(547,4),(553,4),(585,4),(586,4),(600,4),(619,7),(633,8),(634,7),(771,4),(778,4),(258,1),(811,7),(819,8),(825,7),(826,7),(843,7),(858,8)]
theorem prior : Known true entries := (consFace h65_1 (consFace h144_1 (consFace h209_4 (consFace h216_4 (consFace h593_4 (consFace h81_2 (consFace h594_4 (consFace h658_4 (consFace h664_4 (consFace h723_7 (consFace h729_7 (consFace h730_7 (consFace h1089_2 (consFace h1091_4 (consFace h1097_4 (consFace h1161_4 (consFace h1162_4 (consFace h1176_4 (consFace h1227_7 (consFace h1241_8 (consFace h1242_7 (consFace h1539_4 (consFace h1546_4 (consFace h514_1 (consFace h1611_7 (consFace h1619_8 (consFace h1625_7 (consFace h1626_7 (consFace h1675_7 (consFace h1690_8 (known_down baseKnown)))))))))))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 128 0xe0e021f31f01ee060f0f00f0080ffff,padColumn 128 0x202000f34e003e8601af60d00002251),(padColumn 128 0x701c603e03e001f80f003003001e00,padColumn 128 0x20082836412000a84fa43a03049e04),(padColumn 128 0x0,padColumn 128 0x0),(padColumn 128 0x30006181c00c01018300003ffc00e000,padColumn 128 0x2000408140048981810000135a08e808),(padColumn 128 0xc18181fe000001fe040fffc00fff0000,padColumn 128 0x408081fc210000320003388000210000),(padColumn 128 0x1fe000000fe0007f000000fffffff,padColumn 128 0x17e000000fc0007e000000fdeddae),(padColumn 128 0x1fe0000000f000007fffffff0000000,padColumn 128 0x97e0000008b100006fcc72ca0101030),(padColumn 128 0x0,padColumn 128 0x0)] i else tableBits #[(padColumn 128 0xfe000000000ffffff800000000000000,padColumn 128 0xbe080000000edfcd50800000c00000c0),(padColumn 128 0xfffffffffff000000000000000000000,padColumn 128 0xcdcd9350890000100000080000600100),(padColumn 128 0x0,padColumn 128 0x0)] i))
def cols : List ColumnInfo := [(848,10,33,0,1),(792,66,33,0,1),(808,3,80,0,1),(528,265,0,98,2),(776,2,113,0,4),(771,0,120,0,4),(769,2,120,0,4),(592,10,33,256,2),(578,8,305,0,4),(576,10,49,256,3),(577,8,306,0,4),(552,1,338,0,4),(546,1,344,0,4),(520,1,338,32,5),(520,0,371,0,7),(514,1,344,32,5),(514,0,377,0,7),(513,0,378,0,7),(26,320,545,0,2),(280,64,547,0,4),(82,256,553,0,4),(306,0,585,0,4),(50,256,585,0,4),(273,32,586,0,4),(291,0,600,0,4),(272,0,619,0,7),(258,0,633,0,8),(257,0,634,0,7),(24,98,0,769,2),(56,64,771,0,4),(81,32,778,0,4),(24,65,258,544,3),(80,0,811,0,7),(72,0,819,0,8),(66,0,825,0,7),(65,0,826,0,7),(48,0,843,0,7),(33,0,858,0,8)]
def data11 : Nat → Nat := (fun i => tableWord #[0xff,0x216a503] i)
def data10 : Nat → Nat := (fun i => (if i<8 then tableWord #[0x1ff420,0xc28028e466822508,0x1ff460,0x61b48480d32787a509,0x1ffc60,0x10a01a94819464c7a40a,0x1ff4a0,0x5a4044d214a4c62309] i else (if i<16 then tableWord #[0x1ff4e0,0x348030e156929108,0x1ffce0,0x2038d20089441108,0x1ff0e3,0x2064d241c5501108,0x1ff4e3,0x30903394d0e49690110a] i else tableWord #[0x1ff8e3,0x848194844d251c58ba00b] i)))
def data9 : Nat → Nat := bookData 2 3 3 (fun i => (((fun i => tableWord #[0x4e04e3ce04a0c604208e3460] i)) (i/16) >>> (12*(i%16))) % 4096) (fun i => (((fun i => tableWord #[0x3fffbff7bfffebfaef] i)) (i/16) >>> (10*(i%16))) % 1024) (fun i => (((fun i => tableWord #[0xce04128108e8693a1a8a8692a1a868691a1a84869121a4e0492812460491012408262200,0x4a8751a1d4c05138e34e86d0a1b8e8613a188a8612a18888a238e04e3834058c61811860,0x4a3dd38f44e5c138f04a1c118704e5ca38f24e3ca28f24a3cb18b2462c93a1940867401e,0xd00d940368a3d628f7] i)) (i/16) >>> (18*(i%16))) % 262144) (variableSlot (fun i => tablePair #[(0x27c24f22a2172041de1ca17d13811d0ef0cb0b5078064038000,0xa0689928602cc8c782c12858150b0284144c601304c0be0e0638260a141a30133051b23250f060b088160a0700882050602e88830602460205f1c13259a0d0c07c0002d191e130c05e199da0d1e0c06),(0x1fe1e01ab19517014b13811c0e70ba09507104d02701400a000,0x210a1d03a528e820408834624059200a0c04c8690060241402d1e0c039928a0306860370183c784c1664a3c1609a4a3c1809a4a1e3c0900688860241e0280601),(0x22120c1ef1c91a418716713b1170fc0e10c60ab07d04902d000,0x110f029918781c63a3c1a09e0f241104f910e81d2878b81e8882830782e828307825060f03c0a1e078143c0e028681c62612141a0b43c082c40220da3c1807411130a0c05),(0x6c057032015000,0x8878179943c44126461e0710f02)] i))
def data8 : Nat → Nat := (fun i => (if i<24 then (if i<8 then tableWord #[0x4fe128440420,0x0,0x4fe128460420,0x1e01,0x47f8e9448420,0x0,0x4ef889468420,0x1e0402] i else (if i<16 then tableWord #[0x4fb4498a8420,0x1301,0x4fed09ce0460,0x0,0x4f7128461460,0x0,0x4efd244a8460,0x1701] i else tableWord #[0x4efd244e8460,0x0,0x4fbd224a8ce0,0x1301,0x7fc461460420,0x24a1702,0x4ff869448420,0x0] i)) else (if i<32 then tableWord #[0x67f4e58e8420,0xd01,0x5df8a9462420,0x0,0x5fb4498e3420,0x0,0x5fbd224e5420,0x0] i else (if i<40 then tableWord #[0x6ef888461460,0x11b01,0x6ef8884a1460,0x0,0x7774e54e3460,0xf01,0x6ef8884e3460,0x0] i else tableWord #[0x6ef4e5888460,0xd01,0x4ff4e98a8460,0x0,0x4ff5098a3ce0,0x0,0x5efd245004e3,0x0] i))))
def data7 : Nat → Nat := (fun i => tableWord #[0xcaf8c9888461460,0x0,0xaebd424e5888460,0x0] i)
def levels : Nat → Packing
  | 7 => (2,4,6,0,0,0,0,data7)
  | 8 => (24,3,6,0,0,0,0,data8)
  | 9 => (52,2,6,0,0,0,0,data9)
  | 10 => (9,1,6,0,0,0,0,data10)
  | 11 => (1,0,6,0,0,0,0,data11)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun v => (if v=7025981528652627411 then some (1,0) else (if v=5611940961228524796 then some (0,0) else none))
  | 9 => fun h => smallSlot h 12 43 5 4 (fun i => (((fun i => tableWord #[0x990221a4001806b] i)) (i/16) >>> (5*(i%16))) % 32) (fun i => (((fun i => tableWord #[0xa10c0f401e07000216e5100063380b00021100020cf30,0xe44014e04c1221543533560300500001726f000000002609,0x26e41343120d618e0600a40860ec32] i)) (i/16) >>> (12*(i%16))) % 4096)
  | 10 => fun h => smallSlot h 48 173 6 4 (fun i => (((fun i => tableWord #[0x1e061082e0200c328424,0x46428948e0784100520,0x812218089010b5065c6] i)) (i/16) >>> (5*(i%16))) % 32) (fun i => (((fun i => (if i<8 then tableWord #[0xb5980015688577762050038805a5a0000000cad00150c2d29434,0xc00c020ccf912617a083b32807a0d9a7784cc3108e800210b816,0x60640948b0068a12700e1d1e6668ad09e02a41884ee046059432,0x2169180066000c378000834c86004f40b95800b0085118000049,0x27291c08e5c6c6d0892d132000a8c90a88dc534002707c25b00a,0x4348001de31b3e38c9a2909853f10e3a6432000916d0ad8a2000,0x26800000199d60b92bc00080d127801a03ce1401080010a4882,0xe50f16fadedadc7233bf1078120007a6603a000211a652542c94] i else tableWord #[0x36ba1ac12400070ed8780269330000000000c28000703c48a80e,0xa14800355b044000148a145cb3a4ac8d28440004278000368000,0x114d3544bda42819cd469c4000000c1767a0c66257] i))) (i/16) >>> (13*(i%16))) % 8192)
  | 11 => fun h => smallSlot h 14 48 4 4 (fun i => (((fun i => tableWord #[0x10040080020f3805c0140] i)) (i/16) >>> (6*(i%16))) % 64) (fun i => (((fun i => tableWord #[0xa49d1521844a8d98c9a505000e880000084569bc1823,0x24ad84348001234474158634b01000000a0cd0800207,0x8a9c04b3062ae34218a16560628c00185a6309901009] i)) (i/16) >>> (11*(i%16))) % 2048)
  | _ => fun _ => none
def book : Forest := ⟨891,11,samples,cols,[[],[49,134],[16,133],[16,48,133,101],[48,16,101,133],[48,101],[80,97,131,148],[80,129,99,148],[96,81,131,148,49,16],[96,129,83,148],[128,81,99,148],[128,97,83,148,49,48]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 1 := bandCut 8 false (by decide +kernel)
theorem band11 : CutRow book 11 0 1 := row11_0
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 9 := bandCut 9 false (by decide +kernel)
theorem band10 : CutRow book 10 0 9 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 2 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row9_2 : CutRow book 9 2 33 := bandCut 9 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row9_35 : CutRow book 9 35 17 := bandCut 10 false (by decide +kernel)
theorem combine9_0_35 : CutRow book 9 0 35 := @joinRow book 9 0 2 33 row9_0 row9_2
theorem combine9_0_52 : CutRow book 9 0 52 := @joinRow book 9 0 35 17 combine9_0_35 row9_35
theorem band9 : CutRow book 9 0 52 := combine9_0_52
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 10 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_10 : CutRow book 8 10 14 := bandCut 9 false (by decide +kernel)
theorem combine8_0_24 : CutRow book 8 0 24 := @joinRow book 8 0 10 14 row8_0 row8_10
theorem band8 : CutRow book 8 0 24 := combine8_0_24
set_option maxRecDepth 16000 in
theorem row7_0 : CutRow book 7 0 2 := bandCut 8 false (by decide +kernel)
theorem band7 : CutRow book 7 0 2 := row7_0
theorem checked : mixedTables book 11 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band7
  · exact band8
  · exact band9
  · exact band10
  · exact band11
end B1755_12
theorem h1755_12 : Face true 891 12 :=
  mixedLower (g:=B1755_12.book) (i:=0) (hints:=4345651333)
    (before_sound B1755_12.entries B1755_12.prior) B1755_12.geometry B1755_12.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h477_8 : Face true 253 8 := dropFace 4 587556613 h473_7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1863_8 : Face true 935 8 := carry_of (swaps:=[67,147,132,49,114,97,80]) (by decide +kernel) h477_8
theorem h725_7 : Face true 373 7 := carry_of (swaps:=[33]) (by decide +kernel) h723_7
theorem h732_7 : Face true 380 7 := carry_of (swaps:=[101,16,49,32]) (by decide +kernel) h723_7
theorem h845_6 : Face true 429 6 := carry_of (swaps:=[50,131,99,114]) (by decide +kernel) h461_6
theorem h981_8 : Face true 501 8 := carry_of (swaps:=[132,97,82,49,112]) (by decide +kernel) h855_8
theorem h988_9 : Face true 508 9 := carry_of (swaps:=[50,67,132,99,114,81]) (by decide +kernel) h926_9

namespace B989_11
def entries : List (Nat × Nat) := [(113,4),(120,4),(204,4),(237,6),(249,7),(305,4),(308,4),(340,4),(373,7),(377,7),(369,5),(380,7),(396,4),(429,6),(437,7),(444,7),(476,8),(501,8),(505,8),(508,9)]
theorem prior : Known true entries := (consFace h209_4 (consFace h216_4 (consFace h396_4 (consFace h461_6 (consFace h473_7 (consFace h593_4 (consFace h596_4 (consFace h660_4 (consFace h725_7 (consFace h729_7 (consFace h721_5 (consFace h732_7 (consFace h780_4 (consFace h845_6 (consFace h853_7 (consFace h860_7 (consFace h924_8 (consFace h981_8 (consFace h985_8 (consFace h988_9 (known_down baseKnown)))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 102 0x1a18003011830e060003fff,padColumn 102 0xa19001011814e860001691),(padColumn 102 0x0,padColumn 102 0x0),(padColumn 102 0x3e07e39c1e1e070180380e00,padColumn 102 0x140361080a0a07818ab10e04),(padColumn 102 0x6c0460020e1e0c801ffc03000,padColumn 102 0x44046400040404800b3e03408),(padColumn 102 0x3900781c40fe010ffe00ffc000,padColumn 102 0x1000080400fc00093400004000),(padColumn 102 0x780007f0001f00000ffffff,padColumn 102 0x700007e0001e00000ffa96e),(padColumn 102 0x1f8001f800001ffffff000000,padColumn 102 0x1b8001b800001b6c94c020030),(padColumn 102 0x3e00001ffffffe000000000000,padColumn 102 0x3800001e539094001000040040)] i else tableBits #[(padColumn 102 0x3fffffe0000000000000000000,padColumn 102 0x27e19400000000000010000180),(padColumn 102 0x0,padColumn 102 0x0),(padColumn 102 0x0,padColumn 102 0x0)] i))
def cols : List ColumnInfo := [(268,128,113,0,4),(385,4,120,0,4),(260,128,113,8,5),(256,128,113,12,6),(304,1,204,0,4),(273,32,204,0,4),(272,0,237,0,6),(264,4,113,128,5),(260,0,249,0,7),(196,8,305,0,4),(76,128,305,0,4),(193,8,308,0,4),(64,128,305,12,6),(168,1,340,0,4),(136,4,113,256,5),(136,0,373,0,7),(132,0,377,0,7),(4,128,369,8,6),(129,0,380,0,7),(0,128,369,12,7),(112,1,396,0,4),(81,32,396,0,4),(80,32,396,1,5),(80,0,429,0,6),(72,0,437,0,7),(65,0,444,0,7),(32,1,476,0,8),(8,0,501,0,8),(1,4,120,384,6),(4,0,505,0,8),(1,0,508,0,9),(0,1,476,32,9)]
def data10 : Nat → Nat := (fun i => tableWord #[0xff,0x1fe4431a06] i)
def data9 : Nat → Nat := (fun i => (if i<8 then tableWord #[0x1ff441,0x1c4ba00b05,0x1ff461,0xde8920105,0x1ffc61,0x177d938505,0x1ff4a1,0x3a24103] i else (if i<16 then tableWord #[0x1ff4a3,0x4c725504,0x1ff8a3,0x679f44161507,0x1ff4c3,0x313a48a05,0x1ff8c3,0x75b79f01506] i else tableWord #[0x1ff4c5,0x6fa08b04,0x1ff4e5,0xd231463a21908] i)))
def data8 : Nat → Nat := (fun i => (if i<8 then tableWord #[0x2bf8c8441,0x3f7a02,0x27f8e8461,0x3f7a02,0x2fd4288c3,0x1601,0x2fbd024c5,0x3f7a02] i else (if i<16 then tableWord #[0x2ff8a8461,0x0,0x3df4e54a3,0x1701,0x2ff4e84a3,0x0,0x3df4c58a3,0x605df03] i else tableWord #[0x2ffd034e5,0x7f01] i)))
def levels : Nat → Packing
  | 8 => (9,2,5,0,0,0,0,data8)
  | 9 => (10,1,5,0,0,0,0,data9)
  | 10 => (1,0,5,0,0,0,0,data10)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 9 => fun h => smallSlot h 4 16 4 1 (fun i => (((fun i => tableWord #[0x191] i)) (i/16) >>> (3*(i%16))) % 8) (fun i => (((fun i => tableWord #[0x560000f364e728830062c109a5a6] i)) (i/16) >>> (8*(i%16))) % 256)
  | 10 => fun h => smallSlot h 6 21 4 1 (fun i => (((fun i => tableWord #[0xb20336] i)) (i/16) >>> (4*(i%16))) % 16) (fun i => (((fun i => tableWord #[0xc645b407b322c10955000068d600d2c4,0x196a000083] i)) (i/16) >>> (8*(i%16))) % 256)
  | _ => fun _ => none
def book : Forest := ⟨509,10,samples,cols,[[],[50,134]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 8 false (by decide +kernel)
theorem band10 : CutRow book 10 0 1 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 10 := bandCut 9 false (by decide +kernel)
theorem band9 : CutRow book 9 0 10 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 4 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_4 : CutRow book 8 4 5 := bandCut 9 false (by decide +kernel)
theorem combine8_0_9 : CutRow book 8 0 9 := @joinRow book 8 0 4 5 row8_0 row8_4
theorem band8 : CutRow book 8 0 9 := combine8_0_9
theorem checked : mixedTables book 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band8
  · exact band9
  · exact band10
end B989_11
theorem h989_11 : Face true 509 11 :=
  mixedLower (g:=B989_11.book) (i:=0) (hints:=9177491205)
    (before_sound B989_11.entries B989_11.prior) B989_11.geometry B989_11.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1879_11 : Face true 951 11 := carry_of (swaps:=[66,148,50,100,49,82,129,112]) (by decide +kernel) h989_11
theorem h1882_8 : Face true 954 8 := carry_of (swaps:=[64,144,50,116,83,130,96,16]) (by decide +kernel) h477_8
theorem h1950_12 : Face true 990 12 := carry_of (swaps:=[65,67,112,100,147,80,129,32]) (by decide +kernel) h1755_12
theorem h839_6 : Face true 423 6 := carry_of (swaps:=[131,49,114,97]) (by decide +kernel) h461_6
theorem h597_5 : Face true 309 5 := carry_of (swaps:=[133,117,101,32,48]) (by decide +kernel) h217_5
theorem h469_6 : Face true 245 6 := carry_of (swaps:=[83,115,67,32,96]) (by decide +kernel) h461_6

namespace B983_10
def entries : List (Nat × Nat) := [(113,4),(245,6),(371,7),(373,7),(390,4),(423,6),(437,7),(438,7),(470,7)]
theorem prior : Known true entries := (consFace h209_4 (consFace h469_6 (consFace h723_7 (consFace h725_7 (consFace h774_4 (consFace h839_6 (consFace h853_7 (consFace h854_7 (consFace h918_7 (known_down baseKnown))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 78 0x601800618ce0007fff,padColumn 78 0x2818002184ec002aa3),(padColumn 78 0x37909fc0060100201800,padColumn 78 0x12800b44064188ae1808),(padColumn 78 0xe0199ff200c06000,padColumn 78 0xa0088a9202c46012),(padColumn 78 0x0,padColumn 78 0x0),(padColumn 78 0x81f00261803ffff8000,padColumn 78 0x1300a0180333008000),(padColumn 78 0x1e00007e00c00ffffff,padColumn 78 0x1c00007c00800ff555c),(padColumn 78 0xe000038000fff000000,padColumn 78 0x6000118000ccc000060),(padColumn 78 0x3000003ffff000000000,padColumn 78 0x30020237756010080180)] i else tableBits #[(padColumn 78 0x3fffffc0000000000000,padColumn 78 0x2d6c5400000000100600),(padColumn 78 0x0,padColumn 78 0x0),(padColumn 78 0x0,padColumn 78 0x0)] i))
def cols : List ColumnInfo := [(256,6,113,128,5),(256,2,245,0,6),(4,128,371,0,7),(130,0,373,0,7),(16,96,390,1,5),(16,64,423,0,6),(66,0,437,0,7),(65,0,438,0,7),(32,1,470,0,7)]
def data9 : Nat → Nat := (fun i => tableWord #[0xff,0x537128607] i)
def data8 : Nat → Nat := (fun i => tableWord #[0x1fd461,0x8002,0x1fdce1,0x5f0003,0x1ff4e3,0x142603] i)
def data7 : Nat → Nat := (fun i => tableWord #[0x2fd468ce1,0x0,0x3dd8a3ce1,0x0] i)
def data6 : Nat → Nat := (fun i => tableWord #[0x4dd5098a3ce1,0x0] i)
def levels : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,data6)
  | 7 => (2,2,4,0,0,0,0,data7)
  | 8 => (3,1,4,0,0,0,0,data8)
  | 9 => (1,0,4,0,0,0,0,data9)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 7 => fun v => (if v=7180117499260788955 then some (0,0) else none)
  | 8 => fun v => (if v=7400630320253988423 then some (1,0) else (if v=6262894976702743078 then some (0,0) else none))
  | 9 => fun h => smallSlot h 2 9 2 1 (fun i => (((fun i => tableWord #[0x0] i)) (i/16) >>> (1*(i%16))) % 2) (fun i => (((fun i => tableWord #[0x163066000e80] i)) (i/16) >>> (6*(i%16))) % 64)
  | _ => fun _ => none
def book : Forest := ⟨503,9,samples,cols,[[],[112,97,82,132]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 1 := bandCut 8 false (by decide +kernel)
theorem band9 : CutRow book 9 0 1 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 2 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_2 : CutRow book 8 2 1 := bandCut 9 false (by decide +kernel)
theorem combine8_0_3 : CutRow book 8 0 3 := @joinRow book 8 0 2 1 row8_0 row8_2
theorem band8 : CutRow book 8 0 3 := combine8_0_3
set_option maxRecDepth 16000 in
theorem row7_0 : CutRow book 7 0 2 := bandCut 8 false (by decide +kernel)
theorem band7 : CutRow book 7 0 2 := row7_0
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 1 := bandCut 7 false (by decide +kernel)
theorem band6 : CutRow book 6 0 1 := row6_0
theorem checked : mixedTables book 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band6
  · exact band7
  · exact band8
  · exact band9
end B983_10
theorem h983_10 : Face true 503 10 :=
  mixedLower (g:=B983_10.book) (i:=0) (hints:=4899276677)
    (before_sound B983_10.entries B983_10.prior) B983_10.geometry B983_10.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1289_4 : Face true 649 4 := carry_of (swaps:=[149,101,134,117,67]) (by decide +kernel) h209_4
theorem h1290_4 : Face true 650 4 := carry_of (swaps:=[149,101,134,117,67,16]) (by decide +kernel) h209_4
theorem h1292_4 : Face true 652 4 := carry_of (swaps:=[150,134,117,67,32,16]) (by decide +kernel) h209_4
theorem h1351_6 : Face true 679 6 := carry_of (swaps:=[147,131,82,49,32,97,112]) (by decide +kernel) h461_6
theorem h1357_7 : Face true 685 7 := carry_of (swaps:=[150,134,117,66,32,48]) (by decide +kernel) h473_7
theorem h1293_5 : Face true 653 5 := carry_of (swaps:=[149,101,134,117,66,50]) (by decide +kernel) h217_5
theorem h1487_10 : Face true 751 10 := carry_of (swaps:=[148,67,131,114,97,80]) (by decide +kernel) h983_10
theorem h1501_11 : Face true 765 11 := carry_of (swaps:=[150,134,117,66,32,48]) (by decide +kernel) h989_11
theorem h1607_7 : Face true 807 7 := carry_of (swaps:=[101,149,134,117,33,32,65,48]) (by decide +kernel) h473_7
theorem h1751_11 : Face true 887 11 := carry_of (swaps:=[147,132,48,82,97,112]) (by decide +kernel) h990_11
theorem h1799_7 : Face true 903 7 := carry_of (swaps:=[147,132,66,49,82,97,112]) (by decide +kernel) h473_7
theorem h1871_11 : Face true 943 11 := carry_of (swaps:=[66,50,147,65,99,114,129,80]) (by decide +kernel) h989_11
theorem h861_8 : Face true 445 8 := carry_of (swaps:=[134,117,48,64,32]) (by decide +kernel) h477_8
theorem h1105_4 : Face true 561 4 := carry_of (swaps:=[150,134,118,64]) (by decide +kernel) h209_4
theorem h1369_7 : Face true 697 7 := carry_of (swaps:=[150,134,64]) (by decide +kernel) h473_7
theorem h1621_7 : Face true 821 7 := carry_of (swaps:=[151,133,101,32,48]) (by decide +kernel) h473_7
theorem h1805_7 : Face true 909 7 := carry_of (swaps:=[64,147,132,66,99,82,112]) (by decide +kernel) h473_7
theorem h1820_7 : Face true 924 7 := carry_of (swaps:=[144,131,116,83,96,32,16]) (by decide +kernel) h473_7
theorem h796_5 : Face true 412 5 := carry_of (swaps:=[101,134,117,64,32,16]) (by decide +kernel) h217_5

namespace B1885_11
def entries : List (Nat × Nat) := [(396,4),(404,4),(437,7),(444,7),(445,8),(561,4),(685,7),(697,7),(305,4),(821,7),(825,7),(909,7),(924,7),(412,5)]
theorem prior : Known true entries := (consFace h780_4 (consFace h788_4 (consFace h853_7 (consFace h860_7 (consFace h861_8 (consFace h1105_4 (consFace h1357_7 (consFace h1369_7 (consFace h593_4 (consFace h1621_7 (consFace h1625_7 (consFace h1805_7 (consFace h1820_7 (consFace h796_5 (known_down baseKnown)))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 80 0x33839e1c7018c3000fff,padColumn 80 0x21010e0c7408c32004e7),(padColumn 80 0x0,padColumn 80 0x0),(padColumn 80 0x4c005821fe6303f40380,padColumn 80 0x44005c209e2101b40392),(padColumn 80 0x801c60c18084fc080c00,padColumn 80 0x102041c00054084e04),(padColumn 80 0x6781060107000ff000,padColumn 80 0x278102000700011000),(padColumn 80 0x78003801f8000fffff,padColumn 80 0x58003001f0000eeb18),(padColumn 80 0x0,padColumn 80 0x0),(padColumn 80 0xf8001c001fffff00000,padColumn 80 0xb80018001deaa408020)] i else tableBits #[(padColumn 80 0xf00001fffe0000000000,padColumn 80 0xb00000dd600030000040),(padColumn 80 0xfffffe00000000000000,padColumn 80 0x4e625000080000830000),(padColumn 80 0x0,padColumn 80 0x0)] i))
def cols : List ColumnInfo := [(560,1,396,0,4),(41,512,404,0,4),(520,0,437,0,7),(513,0,444,0,7),(512,0,445,0,8),(392,4,561,0,4),(268,128,561,0,4),(272,0,685,0,7),(260,0,697,0,7),(132,8,305,512,5),(136,0,821,0,7),(132,0,825,0,7),(48,0,909,0,7),(33,0,924,0,7),(0,1,412,544,7)]
def data10 : Nat → Nat := (fun i => tableWord #[0xff,0x38ac27bd08] i)
def data9 : Nat → Nat := (fun i => tableWord #[0x1ff420,0x502,0x1ff440,0x2392104,0x1ff4a0,0x602] i)
def data8 : Nat → Nat := (fun i => tableWord #[0x27f8e8440,0x0] i)
def levels : Nat → Packing
  | 8 => (1,2,4,0,0,0,0,data8)
  | 9 => (3,1,4,0,0,0,0,data9)
  | 10 => (1,0,4,0,0,0,0,data10)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 9 => fun v => (if v=6857493274592517248 then some (0,0) else none)
  | 10 => fun h => smallSlot h 7 28 2 4 (fun i => (((fun i => tableWord #[0x47100a] i)) (i/16) >>> (4*(i%16))) % 16) (fun i => (((fun i => tableWord #[0x3054b00604000003c4e1f5b0fc1b4ce1,0x41d2a2f4e3700363a2004a8a200] i)) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨957,10,samples,cols,[[],[67,149,135],[32,133,151],[32,67,117,152],[48,66,117],[48,66,32,149,135,117],[64,50,32,133,151,117],[64,50,152],[80,114,131,148],[80,114,147,132,64,50,32],[112,82,131,148,50,64,32],[112,82,147,132],[128,146,83,116,50,64,67],[128,146,115,84],[144,130,83,116],[144,130,115,84,64,50,67]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 8 false (by decide +kernel)
theorem band10 : CutRow book 10 0 1 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 3 := bandCut 9 false (by decide +kernel)
theorem band9 : CutRow book 9 0 3 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 1 := bandCut 8 false (by decide +kernel)
theorem band8 : CutRow book 8 0 1 := row8_0
theorem checked : mixedTables book 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band8
  · exact band9
  · exact band10
end B1885_11
theorem h1885_11 : Face true 957 11 :=
  mixedLower (g:=B1885_11.book) (i:=0) (hints:=9127163653)
    (before_sound B1885_11.entries B1885_11.prior) B1885_11.geometry B1885_11.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1359_8 : Face true 687 8 := carry_of (swaps:=[152,117,67,32]) (by decide +kernel) h855_8
theorem h1373_8 : Face true 701 8 := carry_of (swaps:=[150,134,64]) (by decide +kernel) h477_8
theorem h1631_10 : Face true 831 10 := dropFace 12 4295334021 h1619_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1806_8 : Face true 910 8 := carry_of (swaps:=[134,150,50,65]) (by decide +kernel) h924_8
theorem h1823_10 : Face true 927 10 := carry_of (swaps:=[152,117,101,67,32]) (by decide +kernel) h1631_10
theorem h1883_11 : Face true 955 11 := carry_of (swaps:=[64,144,116,83,33,129,96]) (by decide +kernel) h989_11
theorem h1886_11 : Face true 958 11 := carry_of (swaps:=[146,64,84,115,98,128,16]) (by decide +kernel) h989_11

namespace B1887_13
def entries : List (Nat × Nat) := [(308,4),(404,4),(438,7),(445,8),(553,4),(687,8),(697,7),(701,8),(819,8),(831,10),(910,8),(927,10),(943,11),(951,11),(955,11),(957,11),(958,11)]
theorem prior : Known true entries := (consFace h596_4 (consFace h788_4 (consFace h854_7 (consFace h861_8 (consFace h1097_4 (consFace h1359_8 (consFace h1369_7 (consFace h1373_8 (consFace h1619_8 (consFace h1631_10 (consFace h1806_8 (consFace h1823_10 (consFace h1871_11 (consFace h1879_11 (consFace h1883_11 (consFace h1885_11 (consFace h1886_11 (known_down baseKnown))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 105 0x38830a068060610180003ffff,padColumn 105 0x18810a02c060210180001550f),(padColumn 105 0x411c34790c780206004003000,padColumn 105 0x10042804280226144103022),(padColumn 105 0x18600b80013818c07fe800c000,padColumn 105 0x8200b80002808402a6820c044),(padColumn 105 0x60000c1801c0213f8010030000,padColumn 105 0x2000040801d000048010430088),(padColumn 105 0x18006f0001e0041c0001ffc0000,padColumn 105 0x8002f000120001c00001040000),(padColumn 105 0x70001e0007e00001fffffff,padColumn 105 0x50001c0007c00001efaaaf0),(padColumn 105 0x0,padColumn 105 0x0),(padColumn 105 0x78001e00007fffffe0000000,padColumn 105 0x580016000077bb5580800300)] i else tableBits #[(padColumn 105 0x1ff80001fffff80000000000000,padColumn 105 0x17700001d6d95000c0000000c00),(padColumn 105 0x1ffffffe0000000000000000000,padColumn 105 0x1de66aa00002000000603000000),(padColumn 105 0x0,padColumn 105 0x0)] i))
def cols : List ColumnInfo := [(137,512,308,2,5),(43,512,404,0,4),(41,512,404,2,5),(521,0,438,0,7),(514,0,445,0,8),(150,256,553,0,4),(148,256,553,2,5),(272,0,687,0,8),(262,0,697,0,7),(258,0,701,0,8),(12,128,819,0,8),(128,0,831,0,10),(0,128,819,12,10),(17,32,910,0,8),(16,32,910,1,9),(32,0,927,0,10),(0,32,910,17,10),(16,0,943,0,11),(8,0,951,0,11),(4,0,955,0,11),(2,0,957,0,11),(1,0,958,0,11)]
def data12 : Nat → Nat := (fun i => tableWord #[0x1ff,0xb94df1ad14d09] i)
def data11 : Nat → Nat := (fun i => tableWord #[0x3ff107,0x2fc0b30f4070c809,0x3ff507,0x50b30fb31cced74cad0c814110,0x3ff907,0x2c2cc3d0c32d430070880d] i)
def data10 : Nat → Nat := (fun i => tableWord #[0x5fdd21507,0x3a84e5b428106,0x7fdd21507,0x2430103,0x5ff509907,0x2430103] i)
def data9 : Nat → Nat := (fun i => tableWord #[0x9fdd41509907,0x0] i)
def levels : Nat → Packing
  | 9 => (1,3,5,0,0,0,0,data9)
  | 10 => (3,2,5,0,0,0,0,data10)
  | 11 => (3,1,5,0,0,0,0,data11)
  | 12 => (1,0,5,0,0,0,0,data12)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 10 => fun v => (if v=6519371802217686780 then some (0,0) else none)
  | 11 => fun v => (if v=8213273995398048448 then some (2,0) else (if v=8521536674887730965 then some (1,0) else (if v=6519371802217686780 then some (0,0) else none)))
  | 12 => fun h => smallSlot h 2 8 2 1 (fun i => (((fun i => tableWord #[0x1] i)) (i/16) >>> (1*(i%16))) % 2) (fun i => (((fun i => tableWord #[0x174408a3] i)) (i/16) >>> (6*(i%16))) % 64)
  | _ => fun _ => none
def book : Forest := ⟨959,12,samples,cols,[[],[32,67,117,152],[48,66,117],[64,50,152]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row12_0 : CutRow book 12 0 1 := bandCut 9 false (by decide +kernel)
theorem band12 : CutRow book 12 0 1 := row12_0
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 3 := bandCut 10 false (by decide +kernel)
theorem band11 : CutRow book 11 0 3 := row11_0
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 9 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_1 : CutRow book 10 1 2 := bandCut 10 false (by decide +kernel)
theorem combine10_0_3 : CutRow book 10 0 3 := @joinRow book 10 0 1 2 row10_0 row10_1
theorem band10 : CutRow book 10 0 3 := combine10_0_3
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 1 := bandCut 9 false (by decide +kernel)
theorem band9 : CutRow book 9 0 1 := row9_0
theorem checked : mixedTables book 12 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band9
  · exact band10
  · exact band11
  · exact band12
end B1887_13
theorem h1887_13 : Face true 959 13 :=
  mixedLower (g:=B1887_13.book) (i:=0) (hints:=4832196485)
    (before_sound B1887_13.entries B1887_13.prior) B1887_13.geometry B1887_13.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1935_11 : Face true 975 11 := carry_of (swaps:=[148,64,131,114,97,80]) (by decide +kernel) h990_11
theorem h1759_13 : Face true 895 13 := dropFace 4 4345653381 h1755_12 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h2011_13 : Face true 1019 13 := carry_of (swaps:=[148,131,114,97,80]) (by decide +kernel) h1759_13
theorem h2013_13 : Face true 1021 13 := carry_of (swaps:=[148,131,114,97,80]) (by decide +kernel) h1887_13
theorem h2014_13 : Face true 1022 13 := carry_of (swaps:=[132,147,82,97,112]) (by decide +kernel) h1759_13

namespace B2015_15
def entries : List (Nat × Nat) := [(249,7),(252,7),(305,4),(306,4),(308,4),(380,7),(390,4),(404,4),(423,6),(476,8),(462,7),(309,5),(503,10),(509,11),(547,4),(553,4),(585,4),(627,7),(633,8),(649,4),(650,4),(652,4),(679,6),(685,7),(653,5),(751,10),(763,11),(765,11),(253,8),(807,7),(819,8),(826,7),(858,8),(887,11),(891,12),(903,7),(935,8),(943,11),(951,11),(957,11),(959,13),(975,11),(990,12),(1019,13),(1021,13),(1022,13)]
theorem prior : Known true entries := (consFace h473_7 (consFace h476_7 (consFace h593_4 (consFace h594_4 (consFace h596_4 (consFace h732_7 (consFace h774_4 (consFace h788_4 (consFace h839_6 (consFace h924_8 (consFace h910_7 (consFace h597_5 (consFace h983_10 (consFace h989_11 (consFace h1091_4 (consFace h1097_4 (consFace h1161_4 (consFace h1235_7 (consFace h1241_8 (consFace h1289_4 (consFace h1290_4 (consFace h1292_4 (consFace h1351_6 (consFace h1357_7 (consFace h1293_5 (consFace h1487_10 (consFace h1499_11 (consFace h1501_11 (consFace h477_8 (consFace h1607_7 (consFace h1619_8 (consFace h1626_7 (consFace h1690_8 (consFace h1751_11 (consFace h1755_12 (consFace h1799_7 (consFace h1863_8 (consFace h1871_11 (consFace h1879_11 (consFace h1885_11 (consFace h1887_13 (consFace h1935_11 (consFace h1950_12 (consFace h2011_13 (consFace h2013_13 (consFace h2014_13 (known_down baseKnown)))))))))))))))))))))))))))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 166 0x10840030305000030f0300600c06403000007ffff,padColumn 166 0x10840010305000010f0300200c024830000055287),(padColumn 166 0x10009c0c1a0e0ec101bc000300080c0008003000,padColumn 166 0x880c020406410094000314080c0488203012),(padColumn 166 0x2600000f01c0000020640d8e3fe1030001000c000,padColumn 166 0x2200000f01c000002024048a1461030091040c024),(padColumn 166 0xc808f60ffe030700c0780011c01803fffe0070000,padColumn 166 0x40003203fe010300ca780001c01001521e0870040),(padColumn 166 0x3007307f0000c1810ff80321e0001fc0003ff80000,padColumn 166 0x1002107faa40400007380201e80003400002080000),(padColumn 166 0x3f8000000001f000003e0001e000003fffffff,padColumn 166 0x2f8000000001e000003c0001c000003df2ad78),(padColumn 166 0x7c000000001fe000003c00001ffffffc0000000,padColumn 166 0x4c0000000014c000000c0000064aace00000180),(padColumn 166 0xf800000000fe00000003fffffe00000000000000,padColumn 166 0xd800000000ee00000003b742b801000000000600)] i else tableBits #[(padColumn 166 0x3f0000000000fffffffffc00000000000000000000,padColumn 166 0x2d000a000080b9e9b8c52800100000007001040800),(padColumn 166 0x3fffffffffff000000000000000000000000000000,padColumn 166 0x3ae7bc52c010000000000000802002008006000000),(padColumn 166 0x0,padColumn 166 0x0)] i))
def cols : List ColumnInfo := [(772,2,249,0,7),(769,2,252,0,7),(718,0,305,0,4),(710,8,305,0,4),(709,8,306,0,4),(707,8,308,0,4),(203,512,308,0,4),(646,8,305,64,5),(643,8,308,64,5),(643,0,380,0,7),(568,65,390,0,4),(107,512,404,0,4),(536,64,423,0,6),(547,0,476,0,8),(546,1,476,0,8),(528,1,462,32,8),(514,8,309,192,7),(520,0,503,0,10),(514,0,509,0,11),(284,192,547,0,4),(212,256,553,2,5),(182,256,585,0,4),(268,128,627,0,7),(386,4,633,0,8),(358,16,649,0,4),(118,256,649,0,4),(357,16,650,0,4),(116,256,649,2,5),(355,16,652,0,4),(112,256,649,6,6),(280,68,547,128,5),(280,64,679,0,6),(338,0,685,0,7),(259,16,652,96,6),(258,16,653,96,7),(272,0,751,0,10),(264,4,627,128,8),(260,0,763,0,11),(258,0,765,0,11),(256,2,253,512,9),(152,64,807,0,7),(72,128,819,4,9),(197,0,826,0,7),(165,0,858,0,8),(136,0,887,0,11),(132,0,891,0,12),(56,64,903,0,7),(88,0,935,0,8),(24,64,935,0,8),(80,0,943,0,11),(72,0,951,0,11),(66,0,957,0,11),(64,0,959,0,13),(48,0,975,0,11),(33,0,990,0,12),(4,0,1019,0,13),(2,0,1021,0,13),(1,0,1022,0,13)]
def data14 : Nat → Nat := (fun i => tableWord #[0x3ff,0xd384b1ca6b7608] i)
def data13 : Nat → Nat := (fun i => tableWord #[0x7ff483,0x18315b486a3f1db6b20a,0x7ff503,0x228d5ed649bb1608,0x7ff523,0x71479959265b7b1109] i)
def data12 : Nat → Nat := (fun i => (if i<8 then tableWord #[0xbbf8ca483,0xf83132d2e6f6ed2e08,0xff7503483,0x24306632edf6230508,0xfbf8ca483,0x32e6d2f9f821ed2e08,0xbff50a483,0x243023f92966b22a0e65b518050d] i else (if i<16 then tableWord #[0xbff90a483,0x3709ed66f9572e07,0xbffd44503,0x320da671f61c1607,0xfff50a483,0x24b23230231e1c07,0xfff528483,0x128151ab266edf611230a] i else tableWord #[0xfff544503,0x24303223081906,0xfff524503,0xf240600052eedf611230a,0xfff504523,0x11ad0220edf6012e91630a] i)))
def data11 : Nat → Nat := (fun i => (if i<16 then (if i<8 then tableWord #[0x13bfd6650a483,0xb2822ae2e04,0x1fe7524503483,0xe1c02,0x1fb78ca503483,0x7e45c0303,0x1ef7528503483,0x7e43a0303] i else tableWord #[0x1bbf50b8ca483,0x3e1c02,0x1bbf5288ca483,0x1edda82808e605,0x1bbf50a8ca483,0x803c1c03,0x1bbfd6650a483,0xbc101803] i) else (if i<24 then tableWord #[0x13ff52b50a483,0x27180cc0e1c05,0x13ff92b50a483,0x161302,0x13ff52b90a483,0x6b0181c03,0x17bfd66544503,0x360502] i else tableWord #[0x13ff52bd44503,0x13898280b04,0x1fbf5288ca483,0x84c8602204] i)))
def data10 : Nat → Nat := (fun i => tableWord #[0x3ce7528524503483,0x501c02,0x2bbdd815288ca483,0x0,0x3bbdd815288ca483,0xe601] i)
def levels : Nat → Packing
  | 10 => (3,4,6,0,0,0,0,data10)
  | 11 => (14,3,6,0,0,0,0,data11)
  | 12 => (11,2,6,0,0,0,0,data12)
  | 13 => (3,1,6,0,0,0,0,data13)
  | 14 => (1,0,6,0,0,0,0,data14)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 11 => fun h => smallSlot h 2 10 2 2 (fun i => (((fun i => tableWord #[0x1] i)) (i/16) >>> (1*(i%16))) % 2) (fun i => (((fun i => tableWord #[0xdf3c400880] i)) (i/16) >>> (7*(i%16))) % 128)
  | 12 => fun h => smallSlot h 7 29 4 2 (fun i => (((fun i => tableWord #[0x2981] i)) (i/16) >>> (2*(i%16))) % 4) (fun i => (((fun i => tableWord #[0x42326824e847342e00005320d6e058028e00,0x1e6ca017c400007548400a9f280143] i)) (i/16) >>> (9*(i%16))) % 512)
  | 13 => fun h => smallSlot h 7 23 4 2 (fun i => (((fun i => tableWord #[0x5008150] i)) (i/16) >>> (4*(i%16))) % 16) (fun i => (((fun i => tableWord #[0xa482f1469ab802240003912c9d5b112328c1,0x20e0a00017980186] i)) (i/16) >>> (9*(i%16))) % 512)
  | 14 => fun h => smallSlot h 2 14 2 2 (fun i => (((fun i => tableWord #[0x0] i)) (i/16) >>> (1*(i%16))) % 2) (fun i => (((fun i => tableWord #[0x310001b424e00cd3] i)) (i/16) >>> (7*(i%16))) % 128)
  | _ => fun _ => none
def book : Forest := ⟨1023,14,samples,cols,[[],[32,67,117,152],[80,97,114,131,148],[112,97,82,147,132]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row14_0 : CutRow book 14 0 1 := bandCut 10 false (by decide +kernel)
theorem band14 : CutRow book 14 0 1 := row14_0
set_option maxRecDepth 16000 in
theorem row13_0 : CutRow book 13 0 3 := bandCut 11 false (by decide +kernel)
theorem band13 : CutRow book 13 0 3 := row13_0
set_option maxRecDepth 16000 in
theorem row12_0 : CutRow book 12 0 1 := bandCut 10 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_1 : CutRow book 12 1 5 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_6 : CutRow book 12 6 5 := bandCut 12 false (by decide +kernel)
theorem combine12_0_6 : CutRow book 12 0 6 := @joinRow book 12 0 1 5 row12_0 row12_1
theorem combine12_0_11 : CutRow book 12 0 11 := @joinRow book 12 0 6 5 combine12_0_6 row12_6
theorem band12 : CutRow book 12 0 11 := combine12_0_11
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 1 := bandCut 10 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_1 : CutRow book 11 1 12 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_13 : CutRow book 11 13 1 := bandCut 12 false (by decide +kernel)
theorem combine11_0_13 : CutRow book 11 0 13 := @joinRow book 11 0 1 12 row11_0 row11_1
theorem combine11_0_14 : CutRow book 11 0 14 := @joinRow book 11 0 13 1 combine11_0_13 row11_13
theorem band11 : CutRow book 11 0 14 := combine11_0_14
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 2 := bandCut 10 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_2 : CutRow book 10 2 1 := bandCut 11 false (by decide +kernel)
theorem combine10_0_3 : CutRow book 10 0 3 := @joinRow book 10 0 2 1 row10_0 row10_2
theorem band10 : CutRow book 10 0 3 := combine10_0_3
theorem checked : mixedTables book 14 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band10
  · exact band11
  · exact band12
  · exact band13
  · exact band14
end B2015_15
theorem h2015_15 : Face true 1023 15 :=
  mixedLower (g:=B2015_15.book) (i:=0) (hints:=4882524037)
    (before_sound B2015_15.entries B2015_15.prior) B2015_15.geometry B2015_15.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h2389_7 : Face true 1205 7 := carry_of (swaps:=[164,148,64,128,116,50,82,96]) (by decide +kernel) h473_7
theorem h2445_7 : Face true 1229 7 := carry_of (swaps:=[165,149,118,133,66]) (by decide +kernel) h473_7
theorem h2521_8 : Face true 1273 8 := carry_of (swaps:=[162,146,100,83,130,112]) (by decide +kernel) h477_8
theorem h2524_8 : Face true 1276 8 := carry_of (swaps:=[162,146,50,67,64,84,99,114,128,16]) (by decide +kernel) h477_8
theorem h2525_11 : Face true 1277 11 := carry_of (swaps:=[168,134,150,117,48,64,32]) (by decide +kernel) h1885_11
theorem h2631_7 : Face true 1319 7 := carry_of (swaps:=[166,101,149,134,117,66,16,48]) (by decide +kernel) h473_7
theorem h2643_7 : Face true 1331 7 := carry_of (swaps:=[160,48,147,128,64,100,50,33,113,80]) (by decide +kernel) h473_7
theorem h2645_8 : Face true 1333 8 := carry_of (swaps:=[166,118,151,101,133,33,50,16,64]) (by decide +kernel) h924_8
theorem h2646_7 : Face true 1334 7 := carry_of (swaps:=[160,144,112,16,132,80,97,32]) (by decide +kernel) h723_7
theorem h2710_7 : Face true 1366 7 := carry_of (swaps:=[160,144,112,132,80,97,32]) (by decide +kernel) h723_7
theorem h2903_11 : Face true 1463 11 := carry_of (swaps:=[166,150,117,66,48]) (by decide +kernel) h990_11
theorem h2974_11 : Face true 1502 11 := carry_of (swaps:=[165,118,149,66]) (by decide +kernel) h990_11
theorem h2895_10 : Face true 1455 10 := carry_of (swaps:=[166,150,117,66,48]) (by decide +kernel) h987_10
theorem h3023_11 : Face true 1519 11 := dropFace 64 4882196357 h2895_10 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h3030_9 : Face true 1526 9 := dropFace 1088 2203926726528 h854_7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h3035_11 : Face true 1531 11 := carry_of (swaps:=[166,117,66,48]) (by decide +kernel) h3023_11
theorem h3037_13 : Face true 1533 13 := carry_of (swaps:=[163,65,50,132,83,146,97,112]) (by decide +kernel) h1887_13
theorem h3143_7 : Face true 1575 7 := carry_of (swaps:=[133,168,149,117,101,50,32,64]) (by decide +kernel) h723_7
theorem h3155_7 : Face true 1587 7 := carry_of (swaps:=[134,168,150,118,64]) (by decide +kernel) h723_7
theorem h3291_11 : Face true 1659 11 := carry_of (swaps:=[161,148,33,116,99,32,81,128]) (by decide +kernel) h990_11
theorem h3341_8 : Face true 1677 8 := carry_of (swaps:=[134,168,150,50,16,64]) (by decide +kernel) h924_8
theorem h3342_7 : Face true 1678 7 := carry_of (swaps:=[160,64,147,132,66,99,82,112,16]) (by decide +kernel) h473_7
theorem h3399_8 : Face true 1703 8 := carry_of (swaps:=[66,162,32,148,33,100,82,113,128]) (by decide +kernel) h855_8
theorem h3339_7 : Face true 1675 7 := carry_of (swaps:=[64,164,16,145,112,67,131,97,80]) (by decide +kernel) h723_7
theorem h3407_11 : Face true 1711 11 := carry_of (swaps:=[66,164,50,147,64,99,114,81,128]) (by decide +kernel) h990_11
theorem h3471_11 : Face true 1743 11 := carry_of (swaps:=[163,65,145,64,131,114,81,96]) (by decide +kernel) h990_11
theorem h3486_10 : Face true 1758 10 := carry_of (swaps:=[167,118,134,149,65,49,16,32]) (by decide +kernel) h987_10
theorem h3335_7 : Face true 1671 7 := carry_of (swaps:=[164,48,144,132,66,49,82,113,96]) (by decide +kernel) h473_7
theorem h3531_9 : Face true 1771 9 := carry_of (swaps:=[152,166,50,32,64]) (by decide +kernel) h3030_9
theorem h3543_11 : Face true 1783 11 := carry_of (swaps:=[152,118,101,165,64,48,32]) (by decide +kernel) h3023_11
theorem h3545_10 : Face true 1785 10 := carry_of (swaps:=[163,65,64,84,131,114,97,144]) (by decide +kernel) h1631_10
theorem h3549_13 : Face true 1789 13 := carry_of (swaps:=[163,65,64,84,131,114,97,144]) (by decide +kernel) h1887_13
theorem h3550_11 : Face true 1790 11 := carry_of (swaps:=[152,166,50,64]) (by decide +kernel) h3023_11
theorem h3591_8 : Face true 1799 8 := carry_of (swaps:=[135,134,167,150,16,64,49,32]) (by decide +kernel) h924_8
theorem h3606_7 : Face true 1814 7 := carry_of (swaps:=[64,161,148,113,100,128,81,32]) (by decide +kernel) h723_7
theorem h3667_9 : Face true 1843 9 := carry_of (swaps:=[50,161,147,67,100,83,32,113,128]) (by decide +kernel) h926_9
theorem h3671_12 : Face true 1847 12 := carry_of (swaps:=[65,164,116,49,100,50,130,81,144]) (by decide +kernel) h1755_12
theorem h3807_15 : Face true 1919 15 := carry_of (swaps:=[162,48,49,148,83,114,97,128]) (by decide +kernel) h2015_15
theorem h3854_9 : Face true 1934 9 := carry_of (swaps:=[67,50,161,148,84,115,130,97]) (by decide +kernel) h926_9
theorem h3855_12 : Face true 1935 12 := carry_of (swaps:=[134,166,117,66,48,16]) (by decide +kernel) h1755_12
theorem h3862_8 : Face true 1942 8 := carry_of (swaps:=[16,64,32,164,145,100,112,130,81,48]) (by decide +kernel) h727_8
theorem h3911_10 : Face true 1959 10 := carry_of (swaps:=[65,67,163,33,116,99,146,81,128]) (by decide +kernel) h1631_10
theorem h3935_15 : Face true 1983 15 := carry_of (swaps:=[67,64,161,50,116,83,146,97,128]) (by decide +kernel) h2015_15
theorem h3999_15 : Face true 2015 15 := carry_of (swaps:=[65,33,160,116,131,146,97,80]) (by decide +kernel) h2015_15
theorem h472_5 : Face true 248 5 := carry_of (swaps:=[100,83,112,32,16]) (by decide +kernel) h217_5
theorem h980_6 : Face true 500 6 := carry_of (swaps:=[33,132,112,82,97,48]) (by decide +kernel) h599_6
theorem h1481_6 : Face true 745 6 := carry_of (swaps:=[148,65,116,129,98,49,80]) (by decide +kernel) h599_6
theorem h1496_6 : Face true 760 6 := carry_of (swaps:=[146,33,65,64,84,128,114,97,48]) (by decide +kernel) h599_6
theorem h1949_11 : Face true 989 11 := carry_of (swaps:=[118,134,149,66,50]) (by decide +kernel) h989_11
theorem h2009_10 : Face true 1017 10 := carry_of (swaps:=[148,131,114,97,80]) (by decide +kernel) h1631_10
theorem h2012_10 : Face true 1020 10 := carry_of (swaps:=[32,64,16,50,148,131,82,113,96]) (by decide +kernel) h1631_10
theorem h2316_4 : Face true 1164 4 := carry_of (swaps:=[166,150,134,117,48,64,32,16]) (by decide +kernel) h209_4
theorem h2565_4 : Face true 1285 4 := carry_of (swaps:=[165,149,134,117,50,66]) (by decide +kernel) h209_4
theorem h2580_4 : Face true 1300 4 := carry_of (swaps:=[166,101,149,134,117,64,32,16]) (by decide +kernel) h209_4
theorem h2641_5 : Face true 1329 5 := carry_of (swaps:=[163,147,128,84,115,96]) (by decide +kernel) h217_5
theorem h2769_6 : Face true 1393 6 := carry_of (swaps:=[160,16,145,64,132,113,98,49,80]) (by decide +kernel) h599_6
theorem h2885_6 : Face true 1445 6 := carry_of (swaps:=[164,65,66,145,116,97,130,49,80]) (by decide +kernel) h599_6
theorem h916_5 : Face true 468 5 := carry_of (swaps:=[132,84,115,96,32,16]) (by decide +kernel) h217_5
theorem h2972_9 : Face true 1500 9 := carry_of (swaps:=[161,66,67,145,100,115,130,81]) (by decide +kernel) h926_9
theorem h3077_4 : Face true 1541 4 := carry_of (swaps:=[101,166,149,134,117,50,32,64]) (by decide +kernel) h209_4
theorem h3665_6 : Face true 1841 6 := carry_of (swaps:=[33,161,146,84,113,98,49,128]) (by decide +kernel) h599_6
theorem h3805_13 : Face true 1917 13 := carry_of (swaps:=[66,162,50,33,148,115,82,97,128]) (by decide +kernel) h1887_13
theorem h3869_11 : Face true 1949 11 := carry_of (swaps:=[135,133,118,166,149,64,32]) (by decide +kernel) h989_11
theorem h3917_10 : Face true 1965 10 := carry_of (swaps:=[67,64,161,50,116,83,146,97,128]) (by decide +kernel) h1631_10
theorem h3925_10 : Face true 1973 10 := carry_of (swaps:=[161,84,115,146,97,128]) (by decide +kernel) h1631_10
theorem h863_9 : Face true 447 9 := dropFace 10 4832196485 h853_7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h3932_9 : Face true 1980 9 := carry_of (swaps:=[49,67,50,164,64,84,115,130,145,96]) (by decide +kernel) h863_9
theorem h3933_13 : Face true 1981 13 := carry_of (swaps:=[67,64,161,50,116,83,146,97,128]) (by decide +kernel) h1887_13
theorem h3997_13 : Face true 2013 13 := carry_of (swaps:=[65,33,160,116,131,146,97,80]) (by decide +kernel) h1887_13
theorem h4045_11 : Face true 2029 11 := dropFace 352 9177163525 h3341_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h4053_11 : Face true 2037 11 := carry_of (swaps:=[149,118,134,165,66,50]) (by decide +kernel) h4045_11
theorem h4057_11 : Face true 2041 11 := carry_of (swaps:=[168,134,150,117,48,64,32]) (by decide +kernel) h4045_11
theorem h4060_11 : Face true 2044 11 := carry_of (swaps:=[117,151,166,133,32,50,64,16]) (by decide +kernel) h4045_11

namespace B4061_15
def entries : List (Nat × Nat) := [(248,5),(476,8),(500,6),(561,4),(600,4),(633,8),(652,4),(745,6),(760,6),(305,4),(957,11),(989,11),(1017,10),(1020,10),(1021,13),(1164,4),(1285,4),(1300,4),(1333,8),(113,4),(1329,5),(1393,6),(1445,6),(468,5),(1500,9),(1533,13),(1541,4),(1677,8),(1789,13),(1841,6),(1917,13),(1949,11),(1965,10),(1973,10),(1980,9),(1981,13),(2013,13),(2029,11),(2037,11),(2041,11),(2044,11)]
theorem prior : Known true entries := (consFace h472_5 (consFace h924_8 (consFace h980_6 (consFace h1105_4 (consFace h1176_4 (consFace h1241_8 (consFace h1292_4 (consFace h1481_6 (consFace h1496_6 (consFace h593_4 (consFace h1885_11 (consFace h1949_11 (consFace h2009_10 (consFace h2012_10 (consFace h2013_13 (consFace h2316_4 (consFace h2565_4 (consFace h2580_4 (consFace h2645_8 (consFace h209_4 (consFace h2641_5 (consFace h2769_6 (consFace h2885_6 (consFace h916_5 (consFace h2972_9 (consFace h3037_13 (consFace h3077_4 (consFace h3341_8 (consFace h3549_13 (consFace h3665_6 (consFace h3805_13 (consFace h3869_11 (consFace h3917_10 (consFace h3925_10 (consFace h3932_9 (consFace h3933_13 (consFace h3997_13 (consFace h4045_11 (consFace h4053_11 (consFace h4057_11 (consFace h4060_11 (known_down baseKnown))))))))))))))))))))))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 164 0xd83067348831c0c83001810c0c600f000007ffff,padColumn 164 0x902043148810c0483000890c04644f0000010951),(padColumn 164 0x0,padColumn 164 0x0),(padColumn 164 0x6004399cb00018300fe360e0fc18070001000f800,padColumn 164 0x400020149000183005a12020541807a101024e804),(padColumn 164 0x821801e0011ce1c30c04071f032007fffe0070000,padColumn 164 0x820801e00014a1430c00011d012011365a0474008),(padColumn 164 0x1060ce00066f0203f01887e0003ff8001fff80000,padColumn 164 0x10404e00042f0201d01007e000339800025080000),(padColumn 164 0xf0000070001c0000f80003c000001ffffffff,padColumn 164 0xb000005000180000f000038000001daf6f6ae),(padColumn 164 0x7f0000078000e0001f000003ffffffe00000000,padColumn 164 0x170000018000a00007000002c466c9800008030),(padColumn 164 0x380000038000300001ffffffc000000000000000,padColumn 164 0x180000028000200001edec2a80080000008000c0)] i else tableBits #[(padColumn 164 0x1c000000c00003ffffe0000000000000000000000,padColumn 164 0xc000000400001ce2a40000400000002000000300),(padColumn 164 0xe0000000fffffc000000000000000000000000000,padColumn 164 0x60000000b76a50000080000030010000003000000),(padColumn 164 0xffffffff000000000000000000000000000000000,padColumn 164 0x9278c14a00008000400004080000000c10c000400)] i))
def cols : List ColumnInfo := [(773,1024,248,0,5),(1569,0,476,0,8),(1033,512,500,0,6),(1480,4,561,0,4),(421,1024,600,0,4),(1412,0,633,0,8),(1408,4,633,0,8),(1377,16,652,0,4),(1044,256,745,0,6),(261,1024,760,0,6),(1156,8,305,576,6),(1088,0,957,0,11),(1056,0,989,0,11),(1028,0,1017,0,10),(1025,0,1020,0,10),(1024,1,476,544,10),(1024,0,1021,0,13),(865,16,1164,0,4),(752,8,1285,0,4),(696,64,1285,0,4),(233,512,1300,0,4),(704,8,1333,0,8),(648,4,113,1280,6),(644,8,1329,64,6),(524,128,1393,0,6),(536,64,1445,0,6),(576,8,1333,128,9),(552,1,468,1024,6),(545,0,1500,0,9),(544,1,476,1024,9),(512,0,1533,0,13),(440,64,1541,0,4),(384,4,633,1024,9),(288,16,1677,64,9),(256,0,1789,0,13),(76,128,1841,0,6),(128,0,1917,0,13),(96,0,1949,0,11),(80,0,1965,0,10),(68,8,1329,640,7),(72,0,1973,0,10),(64,8,1333,640,10),(65,0,1980,0,9),(64,0,1981,0,13),(32,1,476,1536,10),(32,0,2013,0,13),(16,0,2029,0,11),(0,16,1677,352,11),(8,0,2037,0,11),(0,8,1333,704,11),(4,0,2041,0,11),(0,4,633,1408,11),(1,0,2044,0,11),(0,1,476,1568,11)]
def data14 : Nat → Nat := (fun i => tableWord #[0x3ff,0x2b40b92d7a207] i)
def data13 : Nat → Nat := (fun i => tableWord #[0x7ff020,0x5cbd8314bace0508,0x7ff420,0x5cbd83117ace8608,0x7ff820,0xb97b053ad00107] i)
def data12 : Nat → Nat := (fun i => (if i<8 then tableWord #[0xbfb44a020,0x291c0503,0xbfbc4a020,0x281c0503,0xbdf4aa020,0x2a1c0503,0x9ff92a420,0xeb1d0603] i else (if i<16 then tableWord #[0xffe840420,0xaf6f2c5a8605,0xfff062020,0x2e2f31323335280e08140a,0xfff462020,0x2e2f302a29170707,0xfff862020,0x2e2f313428180707] i else tableWord #[0xfff462420,0x2f8c6533290f619d55860a,0xfff862420,0xb38c3233342f6f1d9d030a,0xfff862820,0x31353034160706] i)))
def data11 : Nat → Nat := (fun i => (if i<16 then (if i<8 then tableWord #[0x1bdf0624aa020,0x16a3459834041f06,0x1bdf4624aa020,0xa82e0703,0x1bdf8624aa020,0x300702,0x1bdf5624aa020,0x461302] i else tableWord #[0x1bdf9624aa020,0x4e1f02,0x13ff56a062020,0x5e31198d4101406,0x13ffd6a462020,0x170a02e0704,0x17df8ab462020,0x4c28178a4141106] i) else (if i<24 then tableWord #[0x13ff54b862020,0x170c4300704,0x1ffc861840420,0x2ced20003,0x19ff46292a420,0x12c660f99c3dc2d507,0x19ff86292a420,0x3bc360303] i else tableWord #[0x13ff16a462420,0x5e31198d4320406,0x13ffd4b862420,0xc0121203,0x13ff54b862820,0x2c0702] i)))
def data10 : Nat → Nat := (fun i => tableWord #[0x29df52c0624aa020,0x0,0x23df96c4624aa020,0x0,0x29df8ac46292a420,0x0] i)
def levels : Nat → Packing
  | 10 => (3,4,6,0,0,0,0,data10)
  | 11 => (15,3,6,0,0,0,0,data11)
  | 12 => (11,2,6,0,0,0,0,data12)
  | 13 => (3,1,6,0,0,0,0,data13)
  | 14 => (1,0,6,0,0,0,0,data14)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 11 => fun v => (if v=9929661444464347610 then some (2,0) else (if v=9829307312780417369 then some (1,0) else (if v=6332180413049684947 then some (0,0) else none)))
  | 12 => fun h => smallSlot h 8 31 4 5 (fun i => (((fun i => tableWord #[0x6c6bc8] i)) (i/16) >>> (3*(i%16))) % 8) (fun i => (((fun i => tableWord #[0x406d0be0a000001e0ce04a1460301540b00060fa07a02000,0xc09e0e42ad01000c1c208c0d413805908] i)) (i/16) >>> (12*(i%16))) % 4096)
  | 13 => fun h => smallSlot h 8 30 4 5 (fun i => (((fun i => tableWord #[0x884c1a8800] i)) (i/16) >>> (5*(i%16))) % 32) (fun i => (((fun i => tableWord #[0x825a15005a0aa0900000800000006500020b075211204606,0xe4581200741a202908a1830a803000001c1b107000] i)) (i/16) >>> (12*(i%16))) % 4096)
  | 14 => fun h => smallSlot h 8 36 2 5 (fun i => (((fun i => tableWord #[0x3e9100800] i)) (i/16) >>> (5*(i%16))) % 32) (fun i => (((fun i => tableWord #[0xf4f9164cc1d0d0a6268b16da9908000029b08800,0xc87b3caa82005cb001bb6ad92,0xe8c0000203] i)) (i/16) >>> (10*(i%16))) % 1024)
  | _ => fun _ => none
def book : Forest := ⟨2045,14,samples,cols,[[],[67,149,135],[50,134,169],[50,66,165,134,118,149],[66,50,149,118,134,165],[66,165,118],[32,133,151],[32,67,117,152],[32,48,133,101,151,167],[32,48,64,165,101,118,152],[32,64,48,117,150,134,168],[32,64,165,150,118,133],[48,32,101,133,167,151],[48,32,66,117,134,166,150],[48,101,167],[48,64,149,101,135,167],[48,66,117,166],[48,66,32,149,166,135,117],[64,32,50,101,117,165,152],[64,32,133,118,150,165],[64,48,101,149,167,135],[64,150,168],[64,50,32,133,166,151,117],[64,50,166,152]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row14_0 : CutRow book 14 0 1 := bandCut 10 false (by decide +kernel)
theorem band14 : CutRow book 14 0 1 := row14_0
set_option maxRecDepth 16000 in
theorem row13_0 : CutRow book 13 0 3 := bandCut 11 false (by decide +kernel)
theorem band13 : CutRow book 13 0 3 := row13_0
set_option maxRecDepth 16000 in
theorem row12_0 : CutRow book 12 0 4 := bandCut 10 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_4 : CutRow book 12 4 1 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_5 : CutRow book 12 5 6 := bandCut 12 false (by decide +kernel)
theorem combine12_0_5 : CutRow book 12 0 5 := @joinRow book 12 0 4 1 row12_0 row12_4
theorem combine12_0_11 : CutRow book 12 0 11 := @joinRow book 12 0 5 6 combine12_0_5 row12_5
theorem band12 : CutRow book 12 0 11 := combine12_0_11
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 15 := bandCut 11 false (by decide +kernel)
theorem band11 : CutRow book 11 0 15 := row11_0
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 3 := bandCut 10 false (by decide +kernel)
theorem band10 : CutRow book 10 0 3 := row10_0
theorem checked : mixedTables book 14 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band10
  · exact band11
  · exact band12
  · exact band13
  · exact band14
end B4061_15
theorem h4061_15 : Face true 2045 15 :=
  mixedLower (g:=B4061_15.book) (i:=0) (hints:=9177491205)
    (before_sound B4061_15.entries B4061_15.prior) B4061_15.geometry B4061_15.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

namespace B4063_17
def entries : List (Nat × Nat) := [(252,7),(378,7),(438,7),(462,7),(470,7),(474,7),(476,8),(502,8),(510,11),(619,7),(627,7),(633,8),(634,7),(683,7),(730,7),(762,8),(763,11),(766,10),(819,8),(858,8),(890,9),(891,12),(935,8),(951,11),(954,8),(990,12),(1023,15),(1205,7),(1229,7),(1273,8),(1276,8),(1277,11),(1319,7),(1331,7),(1333,8),(1334,7),(1366,7),(1463,11),(1502,11),(1519,11),(1526,9),(1531,11),(1533,13),(1575,7),(1587,7),(1659,11),(1677,8),(1678,7),(1703,8),(1675,7),(1711,11),(1743,11),(1758,10),(1671,7),(1771,9),(1783,11),(1785,10),(1789,13),(1790,11),(1799,8),(1814,7),(1843,9),(1847,12),(1919,15),(1934,9),(1935,12),(1942,8),(1959,10),(1983,15),(2015,15),(2045,15)]
theorem prior : Known true entries := (consFace h476_7 (consFace h730_7 (consFace h854_7 (consFace h910_7 (consFace h918_7 (consFace h922_7 (consFace h924_8 (consFace h982_8 (consFace h990_11 (consFace h1227_7 (consFace h1235_7 (consFace h1241_8 (consFace h1242_7 (consFace h1355_7 (consFace h1434_7 (consFace h1498_8 (consFace h1499_11 (consFace h1502_10 (consFace h1619_8 (consFace h1690_8 (consFace h1754_9 (consFace h1755_12 (consFace h1863_8 (consFace h1879_11 (consFace h1882_8 (consFace h1950_12 (consFace h2015_15 (consFace h2389_7 (consFace h2445_7 (consFace h2521_8 (consFace h2524_8 (consFace h2525_11 (consFace h2631_7 (consFace h2643_7 (consFace h2645_8 (consFace h2646_7 (consFace h2710_7 (consFace h2903_11 (consFace h2974_11 (consFace h3023_11 (consFace h3030_9 (consFace h3035_11 (consFace h3037_13 (consFace h3143_7 (consFace h3155_7 (consFace h3291_11 (consFace h3341_8 (consFace h3342_7 (consFace h3399_8 (consFace h3339_7 (consFace h3407_11 (consFace h3471_11 (consFace h3486_10 (consFace h3335_7 (consFace h3531_9 (consFace h3543_11 (consFace h3545_10 (consFace h3549_13 (consFace h3550_11 (consFace h3591_8 (consFace h3606_7 (consFace h3667_9 (consFace h3671_12 (consFace h3807_15 (consFace h3854_9 (consFace h3855_12 (consFace h3862_8 (consFace h3911_10 (consFace h3935_15 (consFace h3999_15 (consFace h4061_15 (known_down baseKnown))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 293 0x101cc3077878183c0f0103c103e38000000380f003e0e00180e0f00c3800fc00203fffff,padColumn 293 0x482010858080c030000c100e3a4085000d4f293a2e000c8e0f0063940f408000452c3),(padColumn 293 0x20600000046000c030021c023c3c0060060c01003c00fe00010300004003000040003000,padColumn 293 0x202000000460008020020c0218340020020401001c006a0001034080401320104101300a),(padColumn 293 0x1c0800438878063000000003c3fc00081f8f00603c7ff00661e03ffc3801c00018003c000,padColumn 293 0x800000200180210000004abc3fc1000098500200c4f70022020119c3a01c4841a013c010),(padColumn 293 0x1e00031800f8018400403ce03fc000070e00007803f800000861fc0030001ffffe003c0000,padColumn 293 0x604120804f8108000000c600f4002010200027ca3fac04000001c001000050e9e223e0020),(padColumn 293 0xf0020cf0006000380c0ffc00000781001007ffc000001907e000003ffe00003ffc00000,padColumn 293 0x900004f210200010040ffe81280480000001b34000401007e4081000e60000014400000),(padColumn 293 0xf00000000000ff00000000000001ff80000000001f8000003c00000003ffffffff,padColumn 293 0xb00000000000bf00000000000001ff00000000001f0000003800000003ebbbad3c),(padColumn 293 0x3f0000000003ff0000000000001ffe000000000001e00000003ffffffffc00000000,padColumn 293 0x1700000000027f0000000000001dfe000000000000600000002f319af16000000040),(padColumn 293 0x3c000000007fc0000000000007fe000000000000001ffffffffc00000000000000000,padColumn 293 0xc000000006fc0000000000007ee000000000000001d5fce2e6000200000000000180)] i else tableBits #[(padColumn 293 0xffc00000007f8000000000000007ffffffffffffffffe00000000000000000000000000,padColumn 293 0x1406dc00004005d8280a280000000037df65abe4cb23089400008804000000818000200600),(padColumn 293 0x1ff00000000007ffffffffffffffff80000000000000000000000000000000000000000000,padColumn 293 0x19d800000000077733ccf19330a308400180c000000010000010000800040000010c000800),(padColumn 293 0x1ffffffffffff8000000000000000000000000000000000000000000000000000000000000,padColumn 293 0x1f3ffb38cef200000000000000001000000000000000001800001000000000020010000000)] i))
def cols : List ColumnInfo := [(1793,2,252,0,7),(645,1024,378,0,7),(1609,0,438,0,7),(1584,1,462,0,7),(1576,1,470,0,7),(1572,1,474,0,7),(1570,1,476,0,8),(1552,1,462,32,8),(1545,0,502,0,8),(1540,1,474,32,8),(1538,1,476,32,9),(1537,0,510,0,11),(1424,4,619,0,7),(1416,4,627,0,7),(1414,0,633,0,8),(1410,4,633,0,8),(1409,4,634,0,7),(389,1024,634,0,7),(1364,0,683,0,7),(293,1024,730,0,7),(1296,4,619,128,8),(1288,4,627,128,8),(1282,4,633,128,9),(261,1024,762,0,8),(1284,0,763,0,11),(1281,0,766,0,10),(1100,128,819,0,8),(165,1024,858,0,8),(133,1024,890,0,9),(1156,0,891,0,12),(1048,64,935,0,8),(1096,0,951,0,11),(69,1024,954,0,8),(1057,0,990,0,12),(1024,0,1023,0,15),(840,2,1205,0,7),(816,2,1229,0,7),(772,2,1273,0,8),(769,2,1276,0,8),(770,0,1277,0,11),(768,2,1277,0,11),(720,8,1319,0,7),(708,8,1331,0,7),(706,8,1333,0,8),(705,8,1334,0,7),(681,0,1366,0,7),(644,8,1331,64,8),(580,8,1331,128,8),(578,8,1333,128,9),(584,0,1463,0,11),(560,1,462,1024,8),(552,1,470,1024,8),(548,1,474,1024,8),(546,1,476,1024,9),(545,0,1502,0,11),(528,8,1319,192,9),(528,1,462,1056,9),(528,0,1519,0,11),(516,8,1331,192,9),(514,8,1333,192,10),(521,0,1526,0,9),(520,1,470,1056,9),(516,1,474,1056,9),(516,0,1531,0,11),(514,1,476,1056,10),(514,0,1533,0,13),(408,64,1575,0,7),(332,128,1587,0,7),(400,4,619,1024,8),(392,4,627,1024,8),(386,4,633,1024,9),(385,4,634,1024,8),(388,0,1659,0,11),(354,16,1677,0,8),(353,16,1678,0,7),(337,32,1678,0,7),(280,64,1703,0,8),(324,16,1675,32,8),(322,16,1677,32,9),(321,16,1678,32,8),(336,0,1711,0,11),(289,16,1678,64,8),(304,0,1743,0,11),(289,0,1758,0,10),(264,16,1671,96,9),(276,0,1771,0,9),(272,4,619,1152,9),(260,16,1675,96,9),(258,16,1677,96,10),(257,16,1678,96,9),(264,4,627,1152,9),(264,0,1783,0,11),(262,0,1785,0,10),(258,4,633,1152,10),(257,4,634,1152,9),(258,0,1789,0,13),(257,0,1790,0,11),(184,64,1799,0,8),(233,0,1814,0,7),(204,0,1843,0,9),(76,128,1843,0,9),(200,0,1847,0,12),(128,0,1919,0,15),(81,32,1934,0,9),(112,0,1935,0,12),(105,0,1942,0,8),(88,0,1959,0,10),(24,64,1959,0,10),(64,0,1983,0,15),(32,0,2015,0,15),(2,0,2045,0,15)]
def data16 : Nat → Nat := (fun i => tableWord #[0x7ff,0x8b36dd9ba09dd17d0e50b] i)
def data15 : Nat → Nat := (fun i => (if i<8 then tableWord #[0xfff440,0x5f651ce8e5500beeec1d46210c,0xfff460,0x1d68df9d27e8ee4021650a,0xfff500,0x6031e6ec485040e55f210a,0xfff520,0x1d68e6ec65289de84121e50b0c] i else tableWord #[0xfff528,0x5f216865a2edece6e818a1e5280d] i))
def data14 : Nat → Nat := bookData 2 3 3 (fun i => (((fun i => tableWord #[0x520a0118294440] i)) (i/16) >>> (11*(i%16))) % 2048) (fun i => (((fun i => tableWord #[0x7fffdffbffbfffffaffb3ff] i)) (i/16) >>> (13*(i%16))) % 8192) (fun i => (((fun i => tableWord #[0x52b6a42da50b6b589a52049401294b8242d850b621ad846b614010480411810d612652c0,0x90bc948b2502c920b2d62c94a30523c140f0483c24adb52b6d4a2bd636d40ebd626e4ada,0x502d148f3522cd4a32] i)) (i/16) >>> (18*(i%16))) % 262144) (variableSlot (fun i => tablePair #[(0x50a4b34393d038233b2ed2b227420b1cf1781330f00b2059000,0x2c074d1df2ee77d02b0304d05f2c177d0674c0f0c6066fc86ca1b63d01d341753121b2b7c56060bb1e8341906b21b283c23bf9db282fd02b0303d8f4195305d6fd940c110fa3ca5d2006c1bd1e5207b0ba1b06b1e81d860d121f287fd8460305d8f41a0ba300d83588ec84d0e50e8c08c0609b1e82ef97d8480303f4d15df2c75d00607f4192bb1d728181b45e6f6fb33be8d0f945013ec10fb8bbe50e7a03a0609),(0x6d26846255904c446f3f439532c29623f1bb16510e0b7057000,0x30084ca9818340142d08fed0382e900620b4c0ac0a150974ca402c42ed03c690adbe5c90cd6ca9810b03b0e884d065a0154790b4c274d6400e7b8bae86e80e436516e7a042656e90060091684d8b40ec383d9088c30d0f62a08c060de243682ec60391d20394081562d0d00c1005e1b72976420d0bb11d2ec71d03bae900d6590dfb8541490b9442cfb3cc5ecefa3ca600304d82fc847668f311bd864cefa051e5030777e6f64873be8147940c13603a682e97a3019298ac26ffa030bb3016e43067284d81d967d06af2903d8530785580e9a3be5dcefa0560609),(0x1c11340b9072000,0x162d03b72903d9651b3401c9d147966c980fb03174060bb5090902302b14394081be81ff94bdec230141ec5a0305d680a0629805aa056060c)] i))
def data13 : Nat → Nat := bookData 3 5 5 (fun i => (((fun i => tableWord #[0x52846092b46052b46090b460482460d6246052844094b44086b44050044050350050046050b44046b440480440460440,0x52344048344052246050246052046050344090b440522500d62500] i)) (i/16) >>> (24*(i%16))) % 16777216) (fun i => (((fun i => tableWord #[0xfffb6fff3ff5ffdff6ffdcffe7ffbffbff6dffbffa9bfe3ff9dfe7fe,0xffffdffbfffeffefff7ff] i)) (i/16) >>> (14*(i%16))) % 16384) (fun i => (((fun i => tableWord #[0x90b2861aca1462206430e088c38140cc048330242ca088b2812088018b19462c0494c10e3b02218b00462c00,0x42c5324b10c52c4310b16c18b42d4b10ad82393605495284a148d285034a120d2850c41f610e6d8339a1aca6,0x4838a14921252384920e1248380d4120748379940de15047824adc552b7154a1b152c4436054f52863b6210d,0x528a594929690b8594b27592b8554ae1592b82d4ae0b90b82d42e0b524829409f44827d1209e452c9cd4a253,0x524ad54a2ab90baac62eab504aa9412b8524acd4a2b750394548e1044c9b11320c] i)) (i/16) >>> (22*(i%16))) % 4194304) (variableSlot (fun i => tablePair #[(0x3162e72b729223e2181e01bb18315d1380ea0bd08d05d030000,0x2762021e64824422b0089582794448180fc56118363e80d6e543c231d01cc903d85602f1160605f40550301ec0397286a8782dca03a9207e81160603fa2181645a09b21b941ed0842180c09f47ca1a81e09908ba3200c0937e51100604fa15d1900604),(0x4474033b93643232d82b628920c1cc18212a0b508805d02d000,0x7d14c060540141683502b8ad68530050c40f636515adf0bed00282d0881f4530041503103580ec5d0a0400482d07bc160b40ececa1a11e0963e8da03bc87e508e182a3ec118060cf5d0fb1a81180606e01887440975e50101fe80843217621796350342377204382efdc0bbd0a8c2c01bca1774330c01104b87064c1e092c06617c1e09743d04d2b04),(0x4a24404063bb36e32b2e82a626e2181eb1b416611c0a9055000,0x221974408701c901e5114030997438158c90041600acf299d2e8660083fa21c080409740d1281fca0f0602299c0183740401685d0a41306bb794409000d1281aed3b0f4c9434176158168b00cee58d50c08bd0c15683025bfa2182ad0605fa3e517bec0a0460141e8fa3e50984f1180507b1f46d02ed319087612951b280c1740b1f43302e951b280c116198d94560bdd00282d08),(0x4fd4a646240e39c34e3002bf27e2091c819b1440ec0bf04b000,0x158c8768094a81682b0142321977651002a00c1a856168100160bc960b423c2a0d8963683a05e0d42f4d40d0bba0560c057b212b0141ee81583015ec84ac0507aa2edbea0054018355176df5002a00c1a506c0ba1e5d04c0aaa01ba2501a1755401742a3180306bb2e85401827a3650f20b0c23072005088ec3cd960b77e400a80308a8670640802540386c4b1b41d10c06a0aa0c1605d8090a8c845d0a80407),(0x32f2ec28e25822a1f01a31601000db0a2060000,0x4e5210f0371643e06f0a84a10b2605a4ecd80e027c0dc590f8dd05dd0e85e500121c0e83c0e0dd058c2ba6c0ad0e2381c03c72181684c1643a06d8462e53ad1c8705a2ed4009f288f0281d61e8794340001762400e0960bc2d06d80fbe87a098174082586209)] i))
def data12 : Nat → Nat := bookData 4 5 5 (fun i => (((fun i => tableWord #[0x52450344052848344052394b44042c90b46050394b44048390b44048350b44048350044018b48044086b48044090c46044048346044090b46044018b46044052894b44048394b440,0x50352250044c90b46090b52246052450246052848246092b48246052b48246090b48246018b482460482520460] i)) (i/16) >>> (36*(i%16))) % 68719476736) (fun i => (((fun i => tableWord #[0xe7ff5fff7ff67fda7ffcbff9dfe3ffaf7f7efb7fe6ff6efed9ffa9fed3bf,0x36fff5ff9fff9fffbfedffefff5f3feffefbbf] i)) (i/16) >>> (15*(i%16))) % 32768) (fun i => (((fun i => tableWord #[0x44c6314b56b52852e335208cd3aa531098cd3a6334c850311e4304642d2964308448318d41042da108633400,0x92d7494b5d2d8db490b6b25a18c64369050da4140a7052893f6862e8cd801411ed5247ad4a1e092d729235a5,0x14925948cb614931752ccdb68635528c52432d4da874e432d350cb4f636f242d8ca4b2d2] i)) (i/16) >>> (22*(i%16))) % 4194304) (variableSlot (fun i => tablePair #[(0x33c2f52a227023e20c1d81a417d14d1300f30d70bb08904a000,0xd85300925406941a0da83b07a22e85d0084b01f50174199ab04f29d837678413d06c32ee1b04bca0e0064c904c4311427e0604f284fc0c07022004b21a096494602ac51806a5180102d35050145158015742183221809fa0d47e508c018172312e3c252a06e0606),(0x2be28c2672431fe1cf1b119315f12c0e20a308a07003e010000,0x2501602a85d04b01542b01f63742d01f9ba24c1401b03741bc276374a00260b0bc0582c2f0160b3300e81f024301006c14004a31b970e45a1765001b0e65d0346ef2002fa6ec0ad1bb02ec5e53d66ec138174dde5d04d801),(0x1fd1df1ad18917b14711f1060e10c80af096067000,0x11691c017a04c0580ba09403808007c00c3c874374a002530174a001f81000ac0550ac07e04002f02001761680bc8745006e82551501601205e0800e8a003c09)] i))
def data11 : Nat → Nat := (fun i => (if i<8 then tableWord #[0xc3bf94c8cd48350b440,0x9e501,0xeff442e90c483460440,0x0,0xcffc48d42d90c460440,0x0,0xd3bf5288cd48394b440,0x64001] i else (if i<16 then tableWord #[0xb3fddc152848394b440,0xde501,0xf0ff52852450394b440,0x1bb01,0xc7fdd8d42d90b482460,0x45a01,0x87ff5ae92c90b482460,0x2804002] i else tableWord #[0xe4ff52890c92b482460,0x54004002,0x87ff1cd48c44c90b460,0x2804002] i)))
def data10 : Nat → Nat := (fun i => tableWord #[0x153bdde15288cd48394b440,0x0] i)
def levels : Nat → Packing
  | 10 => (1,6,7,0,0,0,0,data10)
  | 11 => (10,5,7,0,0,0,0,data11)
  | 12 => (45,4,7,0,0,0,0,data12)
  | 13 => (76,3,7,0,0,0,0,data13)
  | 14 => (36,2,7,0,0,0,0,data14)
  | 15 => (5,1,7,0,0,0,0,data15)
  | 16 => (1,0,7,0,0,0,0,data16)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 11 => fun v => (if v=10514651931723972104 then some (0,0) else none)
  | 12 => fun h => smallSlot h 5 17 4 3 (fun i => (((fun i => tableWord #[0xe2] i)) (i/16) >>> (2*(i%16))) % 4) (fun i => (((fun i => tableWord #[0x2585e110a008000000074f860038361c01c4f55,0x208] i)) (i/16) >>> (10*(i%16))) % 1024)
  | 13 => fun h => smallSlot h 25 88 6 3 (fun i => (((fun i => tableWord #[0x1900d10700588a0f3a6a,0x2025b2242] i)) (i/16) >>> (5*(i%16))) % 32) (fun i => (((fun i => tableWord #[0x54d41782008ea117c9e2be0fe1de29b4421b0005538158aa,0x20201c000000e0ac19c0361f000c23106a018a8c21424c04,0x951000a8f64600089b028a2cc0ed4a06a00001ec06647c0c,0xdcca1300002df9a000e1400062500020500020700001a000,0x822251a59e27218ca5a2a01679be125ca626c0960dd58e0b,0xc50b46f49e9a408a1014c4a0] i)) (i/16) >>> (12*(i%16))) % 4096)
  | 14 => fun h => smallSlot h 54 203 7 3 (fun i => (((fun i => tableWord #[0x4013214100000c6050008384,0x166020002045810204a2f0828006,0x3c701000039a084c04b0604000,0x78a501c000] i)) (i/16) >>> (7*(i%16))) % 128) (fun i => (((fun i => (if i<8 then tableWord #[0xc1470b12472340004b1e810c1909a90e5a62ac69d54130870000,0x65de2f4000d0a7567090021c4a4624029275440a02830882a41f,0x800000022615560ce22dcc321e304c16c68de0e40eb08844b,0x810509c8611344959ab40004a861ff2d751608e90184c800012c,0x3a300004074c71048000c47e609ac7a7bcbea95524f179846,0x94ce0ac843809343b0d441ac3ea0db73086cf3480f0000000000,0x200fa880001d6beb291e000208c0ca093eb000014bc000c48,0x51a8002998000b05800183a829a22b05991a23141514e1834000] i else tableWord #[0x366400100ef99e02cd64000a4864a113200021ed230990000,0x69f800286850800000008858a5719b0bb076431e0174ec00000c,0x21800190e0000a5000000000080bb4e684c000a11606022e000,0xc96d61f281c2db4aa09780c414d542013a6e49a617e03c266000,0x248082a2711900dc0000000118300000c0d] i))) (i/16) >>> (13*(i%16))) % 8192)
  | 15 => fun h => smallSlot h 26 93 6 3 (fun i => (((fun i => tableWord #[0x4055400120c00001c0a8c000,0x53104000381006] i)) (i/16) >>> (6*(i%16))) % 64) (fun i => (((fun i => tableWord #[0xe01a08a0d000a0fe07000c5ec1a42340cd23c8495af96,0x45c016595643a1c000a2081025f21b41e29fa05a1400044d,0xc9ee9a000000000448a85802b0c41fc89b16000000695119,0x618299d5b703a19087064a88096788000b1aa0e000915012,0x90b215021cdbe8380ba6281d003052e0a604ea1c11c86,0x246000a13624609c22c1765bf59000e45543406] i)) (i/16) >>> (12*(i%16))) % 4096)
  | 16 => fun h => smallSlot h 5 28 3 3 (fun i => (((fun i => tableWord #[0xe2] i)) (i/16) >>> (2*(i%16))) % 4) (fun i => (((fun i => tableWord #[0xba000a60092213b2000000266c14298f2912,0x39200000000169001080143] i)) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨2047,16,samples,cols,[[],[66,165,118],[32,67,117,152],[32,48,64,165,101,118,152],[48,101,167],[48,66,117,166],[64,32,50,101,117,165,152],[64,50,166,152]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row16_0 : CutRow book 16 0 1 := bandCut 11 false (by decide +kernel)
theorem band16 : CutRow book 16 0 1 := row16_0
set_option maxRecDepth 16000 in
theorem row15_0 : CutRow book 15 0 5 := bandCut 12 false (by decide +kernel)
theorem band15 : CutRow book 15 0 5 := row15_0
set_option maxRecDepth 16000 in
theorem row14_0 : CutRow book 14 0 2 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row14_2 : CutRow book 14 2 21 := bandCut 12 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row14_23 : CutRow book 14 23 13 := bandCut 13 false (by decide +kernel)
theorem combine14_0_23 : CutRow book 14 0 23 := @joinRow book 14 0 2 21 row14_0 row14_2
theorem combine14_0_36 : CutRow book 14 0 36 := @joinRow book 14 0 23 13 combine14_0_23 row14_23
theorem band14 : CutRow book 14 0 36 := combine14_0_36
set_option maxRecDepth 16000 in
theorem row13_0 : CutRow book 13 0 6 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_6 : CutRow book 13 6 33 := bandCut 12 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_39 : CutRow book 13 39 29 := bandCut 13 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_68 : CutRow book 13 68 8 := bandCut 14 false (by decide +kernel)
theorem combine13_0_39 : CutRow book 13 0 39 := @joinRow book 13 0 6 33 row13_0 row13_6
theorem combine13_39_37 : CutRow book 13 39 37 := @joinRow book 13 39 29 8 row13_39 row13_68
theorem combine13_0_76 : CutRow book 13 0 76 := @joinRow book 13 0 39 37 combine13_0_39 combine13_39_37
theorem band13 : CutRow book 13 0 76 := combine13_0_76
set_option maxRecDepth 16000 in
theorem row12_0 : CutRow book 12 0 2 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_2 : CutRow book 12 2 14 := bandCut 12 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_16 : CutRow book 12 16 29 := bandCut 13 true (by decide +kernel)
theorem combine12_0_16 : CutRow book 12 0 16 := @joinRow book 12 0 2 14 row12_0 row12_2
theorem combine12_0_45 : CutRow book 12 0 45 := @joinRow book 12 0 16 29 combine12_0_16 row12_16
theorem band12 : CutRow book 12 0 45 := combine12_0_45
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 1 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_1 : CutRow book 11 1 9 := bandCut 12 false (by decide +kernel)
theorem combine11_0_10 : CutRow book 11 0 10 := @joinRow book 11 0 1 9 row11_0 row11_1
theorem band11 : CutRow book 11 0 10 := combine11_0_10
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 11 false (by decide +kernel)
theorem band10 : CutRow book 10 0 1 := row10_0
theorem checked : mixedTables book 16 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band10
  · exact band11
  · exact band12
  · exact band13
  · exact band14
  · exact band15
  · exact band16
end B4063_17
theorem h4063_17 : Face true 2047 17 :=
  mixedLower (g:=B4063_17.book) (i:=0) (hints:=4882524037)
    (before_sound B4063_17.entries B4063_17.prior) B4063_17.geometry B4063_17.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end Engine
end PEqualNP.Outside.L_meta_9752
namespace PEqualNP.Outside.L_meta_9815.Binary
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_9752.Engine (Wire inv comb combine kept Run)
abbrev Sig := BitVec 4096
def zero : Sig := 0
def one : Sig := BitVec.allOnes 4096
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
def bit (i : Fin 4096) (a : Sig) : Bool := a.getLsbD i.val
theorem bit_zero (i) : bit i zero = false := by simp [bit,zero]
theorem bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
theorem bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
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
theorem get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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
theorem extract {u target} (gs : List Gate) (w : List Sig)
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

abbrev Row := Fin 4096
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
def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
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
def inputs : List Sig := [0x3200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x2f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000]
def target : Sig := 0x2afffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffefffefffffffefffffffefffffffefffefffefffffffefffffffefffffffefffffffefffffffefffffffefffffefefffffefefffffffafffffffafffffffafffafffafffffffafffffffafffffafafafafafafffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffefffeffffffeeffffffeeffffffeeffeeffeefffffffefffffffcfffffffefffffffcfffffffefffffffcfffffefefffffcfcfffffffafffffff0fffffffafff0fff0ffffffaaffffff00ffffaaaa00000000
def targetFn (x : Fin 14 → Bool) : Bool := (x 0 && x 8) || (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)
def absent (i : Fin 14) : Row := Fin.ofNat 4096 (([2048, 1024, 2050, 1024, 64, 512, 512, 1, 2052, 1, 16, 4, 4, 1]:List Nat).getD i.val 0)
def present (i : Fin 14) : Row := Fin.ofNat 4096 (([2049, 1025, 2051, 1028, 80, 520, 514, 1025, 2053, 513, 80, 260, 132, 33]:List Nat).getD i.val 0)
def front : List Sig := ([0, 2, 8, 1, 6, 3, 5, 4, 13, 10, 12, 11, 9, 7]:List Nat).map (fun j => inputs.getD j zero)

def sample (r : Row) (i : Fin 14) := bit r (inputs.getD i.val zero)
theorem input_list : List.ofFn (fun i : Fin 14 => inputs.getD i.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list,List.map_ofFn]
  rfl
set_option maxRecDepth 32000
set_option maxHeartbeats 0
theorem target_eq : ∀ r : Row, bit r target=targetFn (sample r) := by decide +kernel
theorem properT : proper target := by unfold proper; decide +kernel
theorem required : (∀ i : Fin 14, bit (absent i) target ≠ bit (present i) target) ∧
    (∀ i j : Fin 14, i≠j → bit (absent i) (inputs.getD j.val zero) = bit (present i) (inputs.getD j.val zero)) := by decide +kernel
def embed (r : PEqualNP.Outside.L_meta_9752.Engine.Row) : Row := ⟨r.val,by have := r.isLt; omega⟩
def proj (w : Sig) : PEqualNP.Outside.L_meta_9752.Engine.Sig := w.setWidth 2048
theorem transport (v : Sig) : PEqualNP.Outside.L_meta_9752.Engine.restrictRows embed (observe v) = PEqualNP.Outside.L_meta_9752.Engine.observe (proj v) := by
  funext r
  simp [PEqualNP.Outside.L_meta_9752.Engine.restrictRows,PEqualNP.Outside.L_meta_9752.Engine.observe,PEqualNP.Outside.L_meta_9752.Engine.bit,observe,bit,embed,proj,BitVec.getLsbD_setWidth,r.isLt]
theorem project_target : proj target=PEqualNP.Outside.L_meta_9752.Engine.graph := by decide +kernel
theorem project_bank : front.map proj = PEqualNP.Outside.L_meta_9752.Engine.zero :: PEqualNP.Outside.L_meta_9752.Engine.zero :: PEqualNP.Outside.L_meta_9752.Engine.zero :: PEqualNP.Outside.L_meta_9752.Engine.inputs := by decide +kernel
theorem physical_binary (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x, C.eval (List.ofFn x)=targetFn x) : 20 ≤ C.gates.countP (fun g => !isNot g) := by
  classical
  have eq : (execute C.gates inputs).getD C.output zero=target := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute C.gates inputs).getD C.output zero) = bit r target
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1),←sampled]
    exact (computes (sample r)).trans (target_eq r).symm
  have out := get_rep (u:=true) (execute C.gates inputs) C.output
  rw [eq] at out
  unfold PEqualNP.Outside.L_meta_9815.Binary.Repr at out
  rw [nrm_id (by decide +kernel : bit 0 target=false)] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates inputs legal (fun h => Bool.noConfusion h) properT (out.resolve_right (fun h => h properT))
  have ns : inputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 14, inputs.getD i.val zero = a := by
    rw [←input_list] at ha
    exact List.mem_ofFn.mp ha
  have eqS : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run inputs (inputs.getD i.val zero) sub (absent i) (present i) (required.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply required.2 i j
      rintro rfl
      exact hn rfl
  have rr := list_run run front (by decide +kernel) ((by decide +kernel : front.toFinset=inputs.toFinset).trans eqS.symm)
  have rootsEq : (front.map observe).map (PEqualNP.Outside.L_meta_9752.Engine.restrictRows embed) =
      (PEqualNP.Outside.L_meta_9752.Engine.zero::PEqualNP.Outside.L_meta_9752.Engine.zero::PEqualNP.Outside.L_meta_9752.Engine.zero::PEqualNP.Outside.L_meta_9752.Engine.inputs).map PEqualNP.Outside.L_meta_9752.Engine.observe := by
    rw [←project_bank,List.map_map,List.map_map]
    apply List.map_congr_left
    intro v _
    exact transport v
  have teq : PEqualNP.Outside.L_meta_9752.Engine.restrictRows embed (observe target)=PEqualNP.Outside.L_meta_9752.Engine.observe PEqualNP.Outside.L_meta_9752.Engine.graph := (transport _).trans (congrArg PEqualNP.Outside.L_meta_9752.Engine.observe project_target)
  have bound : PEqualNP.Outside.L_meta_9752.Engine.Lower true PEqualNP.Outside.L_meta_9752.Engine.inputs PEqualNP.Outside.L_meta_9752.Engine.graph 17 := by
    have b := PEqualNP.Outside.L_meta_9752.Engine.h4063_17
    change PEqualNP.Outside.L_meta_9752.Engine.Lower true (PEqualNP.Outside.L_meta_9752.Engine.varsX 2047) (PEqualNP.Outside.L_meta_9752.Engine.graphGoal 2047) 17 at b
    rwa [show PEqualNP.Outside.L_meta_9752.Engine.varsX 2047=PEqualNP.Outside.L_meta_9752.Engine.inputs by decide +kernel,show PEqualNP.Outside.L_meta_9752.Engine.graphGoal 2047=PEqualNP.Outside.L_meta_9752.Engine.graph by decide +kernel] at b
  have zc : PEqualNP.Outside.L_meta_9752.Engine.Constant (PEqualNP.Outside.L_meta_9752.Engine.observe PEqualNP.Outside.L_meta_9752.Engine.zero) := ⟨false,funext PEqualNP.Outside.L_meta_9752.Engine.bit_zero⟩
  have subr : PEqualNP.Outside.L_meta_9752.Engine.supply true (PEqualNP.Outside.L_meta_9752.Engine.inputs.map PEqualNP.Outside.L_meta_9752.Engine.observe) ((front.map observe).map (PEqualNP.Outside.L_meta_9752.Engine.restrictRows embed)) := by
    rw [rootsEq]
    intro v hv
    simp only [List.map_cons,List.mem_cons,or_self_left] at hv
    rcases hv with rfl|mem
    · exact Or.inr (Or.inl zc)
    · exact Or.inl mem
  have total := PEqualNP.Outside.L_meta_9752.Engine.projected_bound embed rr (by rw [teq]; exact PEqualNP.Outside.L_meta_9752.Engine.observe_proper PEqualNP.Outside.L_meta_9752.Engine.graph_proper)
    (p:=0) PEqualNP.Outside.L_meta_9752.Engine.Reach.start subr (by rw [teq]; exact bound)
  rw [rootsEq] at total
  have one : PEqualNP.Outside.L_meta_9752.Engine.cost (PEqualNP.Outside.L_meta_9752.Engine.observe PEqualNP.Outside.L_meta_9752.Engine.zero)=1 := by simp [PEqualNP.Outside.L_meta_9752.Engine.cost,zc]
  simp only [List.map_cons,PEqualNP.Outside.L_meta_9752.Engine.mass_cons,one] at total
  omega
end PEqualNP.Outside.L_meta_9815.Binary

namespace PEqualNP.Outside.L_meta_9815.SeedDeck
open PEqualNP.Outside.L_meta_9752.Engine
abbrev X := Fin 14 → Bool
def raw (v : Fin 14) : Wire X := fun x => x v
def roots := List.ofFn raw
def edges : List (Fin 14 × Fin 14) := [(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
def goal (m : Nat) (x : X) :=
  edges.any (fun e => m.testBit e.1.val && m.testBit e.2.val && x e.1 && x e.2)
def Bound (mask k : Nat) := ∀ p bank, Reach true roots p bank → Available true bank (goal mask) → k≤p

theorem map_available {R S : Type} {f : S → R} {pool : List (Wire R)}
    {base : List (Wire S)} {a : Wire R} (h : Available true pool a)
    (sup : supply true base (pool.map (restrictRows f))) :
    Available true base (restrictRows f a) := by
  rcases h with m|⟨c,e⟩|⟨_,m⟩
  · exact sup _ (List.mem_map_of_mem (f:=restrictRows f) m)
  · exact Or.inr (Or.inl ⟨c,by rw [e];rfl⟩)
  · have invA := sup _ (List.mem_map_of_mem (f:=restrictRows f) m)
    change Available true base (inv (restrictRows f a)) at invA
    simpa only [inv_inv'] using avail_inv rfl invA

theorem map_reach {R S : Type} {f : S → R} {rr : List (Wire R)} {base : List (Wire S)}
    {p bank} (run : Reach true rr p bank) (initial : supply true base (rr.map (restrictRows f))) :
    ∃ bs, Reach true base p bs ∧ supply true bs (bank.map (restrictRows f)) := by
  induction run using Reach.ind with
  | start => exact ⟨base,Reach.start,initial⟩
  | @two p bank a b op h ha hb ih =>
    obtain ⟨bs,level,sup⟩ := ih
    have aa := map_available ha sup
    have bb := map_available hb sup
    refine ⟨_,Reach.two op level aa bb,?_⟩
    intro v hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    rcases List.mem_cons.mp hw with rfl|m
    · have eq : restrictRows f (combine op a b) = combine op (restrictRows f a) (restrictRows f b) := by
        cases op <;> rfl
      rw [eq]
      exact Or.inl (List.mem_cons_self ..)
    · exact available_cons _ (sup _ (List.mem_map_of_mem (f:=restrictRows f) m))

def image (map : List Nat) (i : Fin 14) := inputs.getD (map.getD i.val 11) zero
def embed (map : List Nat) (r : Row) : X := fun i => bit r (image map i)

theorem seed {m k s : Nat} (map : List Nat) (lower : Face true m k)
    (valid : ∀ i : Fin 14, image map i=zero ∨ image map i∈varsX m)
    (evaluate : ∀ r : Row, goal s (embed map r) = bit r (graphGoal m)) : Bound s k := by
  intro p bank run out
  have initial : supply true ((varsX m).map observe) (roots.map (restrictRows (embed map))) := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    change Available true ((varsX m).map observe) (observe (image map i))
    rcases valid i with z|mem
    · rw [z]
      exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
    · exact Or.inl (List.mem_map_of_mem (f:=observe) mem)
  obtain ⟨bs,hr,hs⟩ := map_reach run initial
  have h := map_available out hs
  have eq : restrictRows (embed map) (goal s)=observe (graphGoal m) := funext evaluate
  rw [eq] at h
  exact lower _ _ hr h

set_option maxHeartbeats 0
set_option maxRecDepth 32000

theorem s6890 : Bound 6890 12 :=
  seed [11, 0, 11, 4, 11, 3, 1, 5, 11, 9, 11, 8, 6, 11] h1755_12 (by decide +kernel) (by decide +kernel)

theorem s7914 : Bound 7914 13 :=
  seed [11, 5, 11, 9, 11, 8, 6, 0, 11, 4, 2, 3, 1, 11] h1759_13 (by decide +kernel) (by decide +kernel)

theorem s8057 : Bound 8057 15 :=
  seed [0, 11, 11, 2, 1, 3, 4, 11, 5, 6, 9, 8, 7, 11] h2015_15 (by decide +kernel) (by decide +kernel)

theorem s12149 : Bound 12149 15 :=
  seed [1, 11, 2, 11, 3, 0, 4, 11, 8, 5, 9, 6, 11, 7] h2015_15 (by decide +kernel) (by decide +kernel)

theorem s12151 : Bound 12151 17 :=
  seed [10, 6, 5, 11, 8, 7, 9, 11, 0, 3, 2, 1, 11, 4] h4063_17 (by decide +kernel) (by decide +kernel)

theorem s15082 : Bound 15082 13 :=
  seed [11, 8, 11, 9, 11, 6, 5, 1, 11, 4, 11, 0, 3, 2] h1759_13 (by decide +kernel) (by decide +kernel)

theorem s16058 : Bound 16058 15 :=
  seed [11, 0, 11, 4, 3, 2, 11, 5, 11, 10, 7, 6, 8, 9] h4061_15 (by decide +kernel) (by decide +kernel)

theorem s16122 : Bound 16122 17 :=
  seed [11, 0, 11, 2, 4, 3, 1, 10, 11, 9, 6, 8, 7, 5] h4063_17 (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_9815.SeedDeck

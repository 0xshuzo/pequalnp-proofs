import PEqualNP.Outside.L_meta_971

namespace PEqualNP.Outside.L_meta_9753.Pair
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 16384
def zero : Sig := 0
def one : Sig := BitVec.allOnes 16384
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
def bit (i : Fin 16384) (a : Sig) : Bool := a.getLsbD i.val
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
abbrev Row := Fin 16384
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
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Input (n : Nat) := Fin n → Bool
def ports (n : Nat) : List (Wire (Input n)) := List.ofFn (fun i x => x i)
def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def wires {n : Nat} (gs : List Gate) (x : Input n) := gs.foldl step (List.ofFn x)
def addr {n : Nat} (gs : List Gate) (v : Wire (Input n)) :=
  ∃ i, i<n+gs.length ∧ ∀ x, (wires gs x).getD i false = v x
def mono (gs : List Gate) := ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem fold_length (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons,ih,step,List.length_append,List.length_cons,List.length_nil]; omega

theorem wire_length {n} (gs : List Gate) (x : Input n) : (wires gs x).length=n+gs.length := by
  simp [wires,fold_length]

theorem wire_snoc {n} (gs : List Gate) (g : Gate) (x : Input n) :
    wires (gs++[g]) x = step (wires gs x) g := by simp [wires]

theorem addr_snoc {n} {gs : List Gate} (g : Gate) {v : Wire (Input n)} (h : addr gs v) :
    addr (gs++[g]) v := by
  obtain ⟨i,lt,eq⟩ := h
  refine ⟨i,by simp; omega,fun x => ?_⟩
  rw [wire_snoc]
  have small : i<(wires gs x).length := (wire_length gs x).symm ▸ lt
  simpa only [step,List.getD_eq_getElem?_getD,List.getElem?_append_left small] using eq x

def makeGate (d : Bool) (i j : Nat) : Gate := ⟨if d then .or else .and,[i,j]⟩
theorem gate_legal (d : Bool) (i j : Nat) :
    (makeGate d i j).op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ (makeGate d i j).inputs.length ≤ 2 := by
  cases d <;> simp [makeGate]

theorem last_value {n} (gs : List Gate) (g : Gate) (x : Input n) :
    (wires (gs ++ [g]) x).getD (n+gs.length) false =
    g.op.eval (g.inputs.map fun i => (wires gs x).getD i false) := by
  rw [wire_snoc,←wire_length gs x]
  simp [step,List.getD_eq_getElem?_getD]

theorem realize {n k bank} (h : Reach false (ports n) k bank) :
    ∃ gs : List Gate, mono gs ∧ gs.length≤k ∧
      ∀ v, Available false bank v → Constant v ∨ addr gs v := by
  induction h using Reach.ind with
  | start =>
    refine ⟨[],by simp [mono],by simp,?_⟩
    intro v hv
    rcases hv with h | h | ⟨bad,_⟩
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
      refine Or.inr ⟨i.val,by simpa using i.isLt,fun x => ?_⟩
      simp [wires,List.getD_eq_getElem?_getD,i.isLt]
    · exact Or.inl h
    · cases bad
  | @two k bank a b d hr ha hb ih =>
    obtain ⟨gs,lg,le,rep⟩ := ih
    by_cases co : Constant a ∨ Constant b
    · refine ⟨gs,lg,by omega,?_⟩
      intro v hv
      rcases hv with hm | h | ⟨bad,_⟩
      · rcases List.mem_cons.mp hm with rfl | old
        · exact rep _ (from_constant d co ha hb)
        · exact rep _ (Or.inl old)
      · exact Or.inl h
      · cases bad
    · obtain ⟨i,li,ai⟩ := (rep _ ha).resolve_left (fun h => co (Or.inl h))
      obtain ⟨j,lj,bj⟩ := (rep _ hb).resolve_left (fun h => co (Or.inr h))
      let g := makeGate d i j
      refine ⟨gs++[g],?_,by simp;omega,?_⟩
      · intro e he
        rcases List.mem_append.mp he with old | last
        · exact lg e old
        · obtain rfl := List.mem_singleton.mp last
          exact gate_legal _ _ _
      · intro v hv
        rcases hv with hm | h | ⟨bad,_⟩
        · rcases List.mem_cons.mp hm with rfl | old
          · refine Or.inr ⟨n+gs.length,by simp,fun x => ?_⟩
            rw [last_value]
            have ax := ai x
            have bx := bj x
            simp only [List.getD_eq_getElem?_getD] at ax bx
            cases d <;> simp [g,makeGate,GateOp.eval,combine,ax,bx]
          · exact (rep _ (Or.inl old)).imp_right (addr_snoc g)
        · exact Or.inl h
        · cases bad

def edgeList : List (Fin 14 × Fin 14) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
def goal (x : Input 14) := edgeList.any (fun e => x e.1 && x e.2)
def edgeListN : List (Nat × Nat) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
theorem sameEdges : edgeList.map (fun e => (e.1.val,e.2.val))=edgeListN := by decide
theorem meaning (x : Input 14) :
    goal x=true ↔ ∃ u v : Fin 14, (u.val,v.val) ∈ edgeListN ∧ x u=true ∧ x v=true := by
  rw [goal,List.any_eq_true,←sameEdges]
  constructor
  · rintro ⟨⟨u,v⟩,h,hv⟩
    exact ⟨u,v,List.mem_map.mpr ⟨(u,v),h,rfl⟩,(Bool.and_eq_true_iff.mp hv).1,(Bool.and_eq_true_iff.mp hv).2⟩
  · rintro ⟨u,v,hm,hu,hv⟩
    obtain ⟨⟨a,b⟩,hab,z⟩ := List.mem_map.mp hm
    have au : a=u := Fin.ext (congrArg Prod.fst z)
    have bv : b=v := Fin.ext (congrArg Prod.snd z)
    subst a; subst b
    exact ⟨(u,v),hab,Bool.and_eq_true_iff.mpr ⟨hu,hv⟩⟩

theorem not_constant_goal : ¬ Constant goal := by
  rintro ⟨v,h⟩
  have one := congrFun h (fun _ => true)
  have none := congrFun h (fun _ => false)
  change true=v at one
  change false=v at none
  cases one.trans none.symm

theorem root_lower {k bank} (run : Reach false (ports 14) k bank)
    (out : Available false bank goal) : 27≤k := by
  obtain ⟨gs,lg,le,rep⟩ := realize run
  obtain ⟨i,_,trace⟩ := (rep _ out).resolve_left not_constant_goal
  have sound (x : Input 14) : (Circuit.mk gs i).eval (List.ofFn x) = true ↔
      ∃ u v : Fin 14, (u.val,v.val) ∈ edgeListN ∧ x u=true ∧ x v=true := by
    change (wires gs x).getD i false=true ↔ _
    rw [trace x]
    exact meaning x
  have bound := PEqualNP.Outside.L_meta_971 (Circuit.mk gs i) lg sound
  change 27≤gs.length at bound
  omega
abbrev X := Input 14
def raw (i : Fin 14) : Wire X := fun x => x i
def pin (i : Fin 14) (x : X) : X := fun j => if j=i then false else x j
def coGoal (i : Fin 14) : Wire X := restrictRows (pin i) goal
def n1 (i : Fin 14) : Fin 14 := ![7,7,8,7,10,9,8,0,0,1,0,3,2,1] i
def n2 (i : Fin 14) : Fin 14 := ![8,9,12,11,11,10,9,1,2,5,4,4,3,2] i
def n3 (i : Fin 14) : Fin 14 := ![10,13,13,12,13,12,11,3,6,6,5,6,5,4] i
def star (i : Fin 14) : Wire X :=
  combine false (raw i) (combine true (raw (n1 i)) (combine true (raw (n2 i)) (raw (n3 i))))

set_option maxHeartbeats 24000000 in
theorem glue (i : Fin 14) : combine true (coGoal i) (star i)=goal := by
  fin_cases i <;> funext x <;>
    simp (config := {decide := true}) [combine,coGoal,star,goal,restrictRows,raw,edgeList,n1,n2,n3,pin,
      List.any, Bool.and_or_distrib_left, Bool.and_or_distrib_right, Bool.and_comm, Bool.or_comm,
      Bool.or_left_comm, Bool.or_assoc] <;> ac_rfl

theorem co_constant (i : Fin 14) : ¬ Constant (coGoal i) := by
  rintro ⟨v,h⟩
  have hi := congrFun h (fun _ => true)
  have lo := congrFun h (fun _ => false)
  have ht : ∀ z, coGoal z (fun _ => true)=true := by decide
  have hf : ∀ z, coGoal z (fun _ => false)=false := by decide
  rw [ht] at hi
  rw [hf] at lo
  cases hi.trans lo.symm

theorem raw_mem (i : Fin 14) : raw i ∈ ports 14 := List.mem_ofFn.mpr ⟨i,rfl⟩
theorem ports_seen {n k bank} (hr : Reach false (ports n) k bank) :
    ∀ w ∈ ports n, w ∈ bank := by
  induction hr using Reach.ind with
  | start => exact fun _ h => h
  | two _ _ _ _ ih => exact fun w h => List.mem_cons_of_mem _ (ih w h)

theorem co_lower (i : Fin 14) {k bank} (hr : Reach false (ports 14) k bank)
    (out : Available false bank (coGoal i)) : 23≤k := by
  have av : ∀ j, Available false bank (raw j) := fun j => Or.inl (ports_seen hr _ (raw_mem j))
  have r1 := Reach.two true hr (av (n2 i)) (av (n3 i))
  have r2 := Reach.two true r1 (available_cons _ (av (n1 i))) (Or.inl (List.mem_cons_self ..))
  have r3 := Reach.two false r2 (available_cons _ (available_cons _ (av i))) (Or.inl (List.mem_cons_self ..))
  have r4 := Reach.two true r3 (available_cons _ (available_cons _ (available_cons _ out))) (Or.inl (List.mem_cons_self ..))
  have final := root_lower r4 (Or.inl (show goal ∈ _ by rw [←glue i]; exact List.mem_cons_self ..))
  have size := final
  omega

def pairWire (i j : Fin 14) : Wire X := combine false (raw i) (raw j)
def bankPair (i j : Fin 14) := [inv (pairWire i j),pairWire i j] ++ ports 14

theorem runs_respect {R} {p n : R} {v : Wire R} {k ws} (h : Run false v k ws)
    (ok : ∀ w∈ws, w p=true → w n=true) : v p=true → v n=true := by
  induction h using Run.ind with
  | stop => exact ok v (by simp)
  | perm p h ih => exact ih (fun w m => ok w (p.mem_iff.mp m))
  | @two k a b rest d hd ka kb h ih =>
    apply ih
    have aa := ok a (by simp)
    have bb := ok b (by simp)
    intro w hw
    rcases List.mem_cons.mp hw with rfl | z
    · have lim : d<2 := hd.resolve_right (fun z => Bool.noConfusion z.1)
      have cs : d=0 ∨ d=1 := by omega
      rcases cs with rfl|rfl
      · change (a p && b p)=true → (a n && b n)=true
        exact fun q => Bool.and_eq_true_iff.mpr ⟨aa (Bool.and_eq_true_iff.mp q).1,bb (Bool.and_eq_true_iff.mp q).2⟩
      · change (a p || b p)=true → (a n || b n)=true
        exact fun q => Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp q).imp aa bb)
    · rcases mem_kept z with rfl | t
      · exact aa
      · rcases mem_kept t with rfl | l
        · exact bb
        · exact ok w (by simp [l])

def single (v : Fin 14) : X := fun j => decide (j=v)
def double (i k : Fin 14) : X := fun j => decide (j=i ∨ j=k)

theorem has_neighbor : ∀ i j : Fin 14, i≠j → ∃ k : Fin 14, k≠i ∧ k≠j ∧
    goal (double i k)=true ∧ goal (single k)=false := by decide +kernel

theorem raw_forced {i j : Fin 14} (ne : i≠j) {k ws}
    (h : Run false goal k ws) (sub : ∀ w∈ws, w∈bankPair i j) : raw i∈ws := by
  classical
  by_contra no
  obtain ⟨t,ti,tj,yes,nay⟩ := has_neighbor i j ne
  have ord : ∀ w∈ws, w (double i t)=true → w (single t)=true := by
    intro w hw
    have incl := sub w hw
    change w ∈ inv (pairWire i j)::pairWire i j::ports 14 at incl
    rcases List.mem_cons.mp incl with rfl | hm
    · simp [inv,pairWire,combine,raw,double,single,ne,Ne.symm ne,tj,Ne.symm tj]
    · rcases List.mem_cons.mp hm with rfl | m
      · simp [pairWire,combine,raw,double,single,ne,Ne.symm ne,tj,Ne.symm tj]
      · obtain ⟨a,rfl⟩ := List.mem_ofFn.mp m
        have ai : a≠i := by rintro rfl;exact no hw
        simp [double,single,ai]
  have contra := runs_respect h ord yes
  rw [nay] at contra
  cases contra

theorem neg_forced {i j : Fin 14} {k ws} (h : Run false goal k ws) (lim : k≤24)
    (sub : ∀ w∈ws, w∈bankPair i j) : inv (pairWire i j)∈ws := by
  classical
  by_contra no
  have reach := Reach.two false (Reach.start (u:=false) (roots:=ports 14))
    (Or.inl (raw_mem i)) (Or.inl (raw_mem j))
  have source : supply false (pairWire i j::ports 14) ws := by
    intro w hw
    have incl := sub w hw
    change w∈inv (pairWire i j)::pairWire i j::ports 14 at incl
    exact Or.inl ((List.mem_cons.mp incl).resolve_left (fun eq => no (eq ▸ hw)))
  obtain ⟨q,B,p,out,small⟩ := contraction not_constant_goal h (ports 14) reach source
  have := root_lower p out
  omega

theorem cost_lo {R} {ws : List (Wire R)} {a : Wire R} (hm : a∈ws) (ca : Constant a) : 1≤mass ws := by
  classical
  induction ws with
  | nil => simp at hm
  | cons w ws ih =>
    rw [mass_cons]
    rcases List.mem_cons.mp hm with rfl | tail
    · simp [cost,ca]
    · have := ih tail
      omega

theorem mass_two {R} {a b : Wire R} {ws : List (Wire R)} (ne : a≠b) (ca : Constant a)
    (cb : Constant b) (ha : a∈ws) (hb : b∈ws) : 2 ≤ mass ws := by
  classical
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    rw [mass_cons]
    rcases List.mem_cons.mp ha with rfl | ta
    · have tail := (List.mem_cons.mp hb).resolve_left ne.symm
      have small := cost_lo tail cb
      simp only [cost,if_pos ca]
      omega
    · rcases List.mem_cons.mp hb with rfl | tb
      · have small := cost_lo ta ca
        simp only [cost,if_pos cb]
        omega
      · have small := ih ta tb
        omega

theorem pair_blocked (i j : Fin 14) (ne : i≠j) {k ws} (lim : k≤24)
    (sub : ∀ w∈ws, w∈bankPair i j) : ¬ Run false goal k ws := by
  intro h
  let restrict := restrictRows (pin i)
  have zeroX : restrict (raw i) = fun _ => false := by funext x;simp [restrict,restrictRows,pin,raw]
  have zeroQ : restrict (pairWire i j) = fun _ => false := by funext x;simp [restrict,restrictRows,pin,raw,pairWire,combine]
  have oneN : restrict (inv (pairWire i j)) = fun _ => true := by funext x;simp [restrict,restrictRows,pin,raw,pairWire,combine,inv]
  have xa := List.mem_map_of_mem (f:=restrict) (raw_forced ne h sub)
  have xb := List.mem_map_of_mem (f:=restrict) (neg_forced h lim sub)
  rw [zeroX] at xa
  rw [oneN] at xb
  have diff : (fun _ : X => false) ≠ (fun _ => true) := by
    intro eq
    cases congrFun eq (fun _ => false)
  have charged := mass_two diff ⟨false,rfl⟩ ⟨true,rfl⟩ xa xb
  have src : supply false (ports 14) (ws.map restrict) := by
    intro w hm
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hm
    have incl := sub v hv
    change v∈inv (pairWire i j)::pairWire i j::ports 14 at incl
    rcases List.mem_cons.mp incl with rfl | q
    · exact Or.inr (Or.inl ⟨true,oneN⟩)
    · rcases List.mem_cons.mp q with rfl | ptr
      · exact Or.inr (Or.inl ⟨false,zeroQ⟩)
      · obtain ⟨t,rfl⟩ := List.mem_ofFn.mp ptr
        by_cases eq : t=i
        · subst t;exact Or.inr (Or.inl ⟨false,zeroX⟩)
        · have e : restrict (raw t)=raw t := by funext x;simp [restrict,restrictRows,pin,raw,eq]
          exact Or.inl (e.symm ▸ raw_mem t)
  have big := projected_bound (pin i) h (co_constant i) (Reach.start (roots:=ports 14)) src
    (fun q B hr out => co_lower i hr out)
  change 23+mass (ws.map restrict) ≤ 0+k at big
  omega
noncomputable def enumX : X ≃ Row :=
  Fintype.equivFinOfCardEq (by norm_num [X,Input,Fintype.card_fun])
noncomputable def encode (w : Wire X) : Sig := table (fun r => w (enumX.symm r))
noncomputable def decode (a : Sig) : Wire X := restrictRows enumX (observe a)
theorem decoded (w : Wire X) : decode (encode w)=w := by
  funext x
  simp only [decode,encode,restrictRows,observe,bit_table,Equiv.symm_apply_apply]
theorem encoded_bit (w : Wire X) (r : Row) : bit r (encode w)=w (enumX.symm r) :=
  bit_table _ _
theorem encoded_ok {w : Wire X} (h : ¬Constant w) : proper (encode w) := by
  constructor
  · intro hz
    apply h
    refine ⟨false,?_⟩
    rw [←decoded w,hz]
    exact funext fun x => bit_zero (enumX x)
  · intro hz
    apply h
    refine ⟨true,?_⟩
    rw [←decoded w,hz]
    exact funext fun x => bit_one (enumX x)

theorem physical_suffix (post : List Gate) (lg : mono post) (roots : List (Wire X))
    (out : Nat) (compute : ∀ x, (post.foldl step (roots.map fun w => w x)).getD out false=goal x) :
    ∃ k ws, k≤post.length ∧ Run false goal k ws ∧ ∀ w∈ws,w∈roots := by
  classical
  have good (g) (hg : g∈post) :
      g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2 := by
    obtain ⟨op,len⟩ := lg g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
    exact ⟨op.imp_right Or.inl,len⟩
  have ok (g) (hg : g∈post) : isNot g=false := by
    have a := (lg g hg).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at a
    rcases a with e | e <;> simp [isNot,e]
  have output : (execute post (roots.map encode)).getD out zero = encode goal := by
    apply bit_ext
    intro r
    rw [←b_read,execute_bits _ _ _ (fun g hg => (good g hg).1),encoded_bit]
    have e : (roots.map encode).map (bit r)=roots.map (fun w => w (enumX.symm r)) := by
      simp only [List.map_map]
      apply List.map_congr_left
      exact fun w _ => encoded_bit w r
    rw [e]
    exact compute (enumX.symm r)
  have properG := encoded_ok not_constant_goal
  have rep := get_rep (u:=false) (execute post (roots.map encode)) out
  rw [output] at rep
  change encode goal ∈ _ ∨ ¬proper (encode goal) at rep
  obtain ⟨k,S,hk,exec,sub⟩ := extract post (roots.map encode) good (fun _ => ok) properG
    (rep.resolve_right fun z => z properG)
  have run := list_run exec S.toList (Finset.nodup_toList _) (by simp)
  have lifted := restrict_run enumX run
  change Run false (decode (encode goal)) k _ at lifted
  rw [decoded] at lifted
  refine ⟨k,(S.toList.map observe).map (restrictRows enumX),hk.trans List.countP_le_length,lifted,?_⟩
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hv
  have hz' := sub z (Finset.mem_toList.mp hz)
  have hmap : (roots.map encode).map (nrm false)=roots.map encode := by simp [nrm_false,Function.comp_def]
  rw [hmap] at hz'
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hz'
  change decode (encode r)∈roots
  rwa [decoded]

def physicalPair (i j : Fin 14) (post : List Gate) (out : Nat) : Circuit :=
  ⟨makeGate false i.val j.val::⟨.not,[14]⟩::post,out⟩
def pRoots (i j : Fin 14) : List (Wire X) := ports 14++[pairWire i j,inv (pairWire i j)]
set_option maxHeartbeats 24000000 in
theorem initial_values (i j : Fin 14) (x : X) :
    step (step (List.ofFn x) (makeGate false i.val j.val)) ⟨.not,[14]⟩ =
      (pRoots i j).map (fun w => w x) := by
  fin_cases i <;> fin_cases j <;> simp [step,pRoots,ports,makeGate,List.map_ofFn,GateOp.eval,List.getD_eq_getElem?_getD,
    pairWire,inv,combine,raw]

theorem no_physical_and_not (i j : Fin 14) (ne : i≠j)
    (post : List Gate) (lg : mono post) (out : Nat) (lim : (physicalPair i j post out).size≤26) :
    ¬∀ x, (physicalPair i j post out).eval (List.ofFn x)=goal x := by
  intro computes
  have total : post.length+2≤26 := by
    change (makeGate false i.val j.val::⟨.not,[14]⟩::post).length≤26 at lim
    simp only [List.length_cons] at lim
    omega
  have run (x) : (post.foldl step ((pRoots i j).map fun w => w x)).getD out false=goal x := by
    rw [←initial_values]
    exact computes x
  obtain ⟨k,ws,hk,exec,atRoots⟩ := physical_suffix post lg (pRoots i j) out run
  apply pair_blocked i j ne (by omega : k≤24) _ exec
  intro w hw
  have m := atRoots w hw
  simpa [pRoots,bankPair,or_comm,or_assoc,or_left_comm] using m


/-- A gate with a pre-supplied truth table is free here even if it is used much later.
All remaining gates must be monotone and physically pay one. -/
inductive Tally (free : List Sig) : List Gate → List Sig → Nat → Prop where
  | nil (w) : Tally free [] w 0
  | donated {g gs w k} (inPool : gv w g ∈ free)
      (later : Tally free gs (w++[gv w g]) k) : Tally free (g::gs) w k
  | ordinary {g gs w k} (legal : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2)
      (later : Tally free gs (w++[gv w g]) k) : Tally free (g::gs) w (k+1)

theorem withPool {free gs w k goalSig} (t : Tally free gs w k) (hp : proper goalSig)
    (atEnd : goalSig ∈ free ++ execute gs w) :
    ∃ q S, q≤k ∧ Live false goalSig q S ∧ ∀ a∈S, a∈free++w := by
  induction t with
  | nil w =>
    refine ⟨0,{goalSig},by omega,Live.stop hp,?_⟩
    intro a ha
    have e : a=goalSig := Finset.mem_singleton.mp ha
    subst a
    exact atEnd
  | @donated g gs w k hg t ih =>
    obtain ⟨q,S,small,live,sub⟩ := ih atEnd
    refine ⟨q,S,small,live,?_⟩
    intro a ha
    have h := sub a ha
    rcases List.mem_append.mp h with h | h
    · exact List.mem_append_left _ h
    · rcases List.mem_append.mp h with h | h
      · exact List.mem_append_right _ h
      · have eq : a=gv w g := by simpa using h
        subst a
        exact List.mem_append_left _ hg
  | @ordinary g gs w k lg t ih =>
    obtain ⟨q,S,small,live,sub⟩ := ih atEnd
    have legal : g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2 := by
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at lg ⊢
      exact ⟨lg.1.imp_right Or.inl,lg.2⟩
    have isGood : isNot g=false := by
      obtain ⟨op,_⟩ := lg
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
      rcases op with e|e <;> simp [isNot,e]
    have z := gate_rep false w g legal (fun _=>isGood)
    have flat : w.map (nrm false)=w := by simp [nrm_false,Function.comp_def]
    rw [flat] at z
    have hrep : represented (free++w) (gv w g) ∨
        (1=1 ∧ witness false (free++w) (gv w g)) := by
      rcases z with h | ⟨_,d,a,b,hd,ha,hb,pa,pb,ne,eq⟩
      · exact Or.inl (h.imp (List.mem_append_right _) id)
      · exact Or.inr ⟨rfl,d,a,b,hd,List.mem_append_right _ ha,List.mem_append_right _ hb,pa,pb,ne,eq⟩
    have incl : ∀ a∈S,a∈(free++w)++[gv w g] := by simpa [List.append_assoc] using sub
    obtain ⟨n,T,hn,run,roots⟩ := pull_gate live hrep incl
    exact ⟨n,T,by omega,run,roots⟩

theorem tallyPrefix {free tail budget} (prefixGates : List Gate) (w : List Sig)
    (ok : mono prefixGates) (after : Tally free tail (execute prefixGates w) budget) :
    Tally free (prefixGates++tail) w (budget+prefixGates.length) := by
  induction prefixGates generalizing w with
  | nil => simpa [execute] using after
  | cons g xs ih =>
    have t := ih (w++[gv w g]) (fun a ha=>ok a (by simp [ha])) after
    simpa [Nat.add_assoc] using Tally.ordinary (ok g (by simp)) t

def credited (i j : Fin 14) := [encode (inv (pairWire i j)),encode (pairWire i j)]
def rawBank := (ports 14).map encode

theorem noTally (i j : Fin 14) (ne : i≠j) (gs : List Gate) (out k : Nat)
    (fan : ∀ g∈gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp))
    (count : Tally (credited i j) gs rawBank k) (price : k≤24)
    (correct : ∀ x : X, (Circuit.mk gs out).eval (List.ofFn x)=goal x) : False := by
  classical
  have bound : (execute gs rawBank).getD out zero=encode goal := by
    apply bit_ext
    intro r
    rw [←b_read,execute_bits _ _ _ fan,encoded_bit]
    have same : rawBank.map (bit r)=List.ofFn (enumX.symm r) := by
      change ((List.ofFn (fun i : Fin 14 => raw i)).map encode).map (bit r)=_
      rw [List.map_ofFn,List.map_ofFn]
      exact congrArg List.ofFn (funext fun i => encoded_bit (raw i) r)
    rw [same]
    exact correct (enumX.symm r)
  have pg := encoded_ok not_constant_goal
  have rep := get_rep (u:=false) (execute gs rawBank) out
  rw [bound] at rep
  have use := rep.resolve_right fun z => z pg
  have mem : encode goal∈execute gs rawBank := by simpa [nrm_false,Function.comp_def] using use
  obtain ⟨q,S,le,run,sub⟩ := withPool count pg (List.mem_append_right _ mem)
  have rr := list_run run S.toList (Finset.nodup_toList _) (by simp)
  have physical := restrict_run enumX rr
  change Run false (decode (encode goal)) q _ at physical
  rw [decoded] at physical
  apply pair_blocked i j ne (by omega : q≤24) _ physical
  intro v hv
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  have m := sub b (Finset.mem_toList.mp hb)
  change b ∈ encode (inv (pairWire i j)) :: encode (pairWire i j) :: (ports 14).map encode at m
  change decode b∈bankPair i j
  rcases List.mem_cons.mp m with eq | m
  · rw [eq,decoded]
    simp [bankPair]
  · rcases List.mem_cons.mp m with eq | m
    · rw [eq,decoded]
      simp [bankPair]
    · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp m
      rw [decoded]
      simp [bankPair,hw]

theorem executeLength (gs : List Gate) (w : List Sig) :
    (execute gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [execute]
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).length = _
    rw [ih]
    simp <;> omega

theorem executeRead (gs : List Gate) (w : List Sig) (j : Nat) (hj : j<w.length) :
    (execute gs w).getD j zero = w.getD j zero := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).getD j zero = _
    have small : j<(w++[gv w g]).length := by simp; omega
    rw [ih _ small]
    simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hj]

theorem rawAndValue (preG : List Gate) (i j : Fin 14) :
    gv (execute preG rawBank) (makeGate false i.val j.val) = encode (pairWire i j) := by
  have size : rawBank.length = 14 := by simp [rawBank,ports]
  have old (a : Fin 14) : (execute preG rawBank).getD a.val zero = encode (raw a) := by
    rw [executeRead _ _ _ (by rw [size]; exact a.isLt)]
    simp [rawBank,ports,List.map_ofFn,raw,List.getD_eq_getElem?_getD]
  apply bit_ext
  intro r
  simp [gv,makeGate,old,bit_prime,bit_one,encoded_bit,raw,pairWire,combine]

def placed (preG middle post : List Gate) (i j : Fin 14) (out : Nat) : Circuit :=
  ⟨preG ++ makeGate false i.val j.val :: (middle ++ ⟨.not,[14+preG.length]⟩ :: post),out⟩

/-- Any placement of the raw AND and its inverter is covered; positive gates may
occur on either side of or between them, with arbitrary sharing and output index. -/
theorem noPlaced (preG middle post : List Gate) (lp : mono preG) (lm : mono middle) (ls : mono post)
    (i j : Fin 14) (ne : i≠j) (out : Nat) (lim : (placed preG middle post i j out).size≤26)
    (correct : ∀ x : X,(placed preG middle post i j out).eval (List.ofFn x)=goal x) : False := by
  let free := credited i j
  let g := makeGate false i.val j.val
  let ng : Gate := ⟨.not,[14+preG.length]⟩
  let w := execute preG rawBank
  let z := gv w g
  let w' := execute middle (w++[z])
  have hz : z=encode (pairWire i j) := rawAndValue preG i j
  have wl : w.length = 14+preG.length := by simp [w,executeLength,rawBank,ports]
  have position : w'.getD (14+preG.length) zero=z := by
    have lt : 14+preG.length<(w++[z]).length := by simp [wl]
    change (execute middle (w++[z])).getD (14+preG.length) zero=_
    rw [executeRead _ _ _ lt,←wl]
    simp [List.getD_eq_getElem?_getD]
  have hneg : gv w' ng=encode (inv (pairWire i j)) := by
    apply bit_ext
    intro r
    simp [ng,gv,position,hz,bit_neg,encoded_bit,inv]
  have q0 : Tally free post (w'++[gv w' ng]) post.length := by
    simpa using tallyPrefix post (w'++[gv w' ng]) ls
      (Tally.nil (free:=free) (execute post (w'++[gv w' ng])))
  have q1 : Tally free (ng::post) w' post.length :=
    Tally.donated (by rw [hneg]; simp [free,credited]) q0
  have q2 := tallyPrefix middle (w++[z]) lm q1
  have q3 : Tally free (g::(middle++ng::post)) w (post.length+middle.length) :=
    Tally.donated (by change z∈free; rw [hz]; simp [free,credited]) q2
  have q4 := tallyPrefix preG rawBank lp q3
  have family (a : Gate) (h : a.op∈({GateOp.and,GateOp.or} : Set GateOp)) :
      a.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h ⊢
    exact h.imp_right Or.inl
  have legal : ∀ a∈preG++g::(middle++ng::post),
      a.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact family _ (lp _ h).1
    rcases List.mem_cons.mp h with rfl | h
    · simp [g,makeGate]
    rcases List.mem_append.mp h with h | h
    · exact family _ (lm _ h).1
    rcases List.mem_cons.mp h with rfl | h
    · simp [ng]
    · exact family _ (ls _ h).1
  have lengths : (preG++g::(middle++ng::post)).length≤26 := lim
  simp at lengths
  exact noTally i j ne _ out _ legal q4 (by omega) correct

end PEqualNP.Outside.L_meta_9753.Pair

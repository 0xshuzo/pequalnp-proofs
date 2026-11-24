import PEqualNP.Defs

-- The Live/Run/Forest verification framework and subgraph lower bounds
-- (known383 and dead) are adapted from PressF10, pequalnp-proofs PR 4332,
-- licensed under Apache-2.0.
namespace PEqualNP.Outside.L_meta_3853
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩


def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

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
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
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

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
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

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
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

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
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

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
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
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed4 : Sig := neg (inputs.getD 4 zero)

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed4_table : ∀ r : Row, bit r seed4 = !(sample r 4) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed4_nonzero : seed4 ≠ zero := by decide +kernel
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

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩

def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
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
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

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

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
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
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
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



def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
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
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

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

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
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

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega



def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

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

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
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

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
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
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
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
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
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
def vertex (m j : Nat) := if m.testBit j then (if m.testBit 9 && j == 4 then neg (inputs.getD 4 zero) else inputs.getD j zero) else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
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
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
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

def supportPairs (baseRow mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,Fin.ofNat 512 baseRow,Fin.ofNat 512 (baseRow ^^^ (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  let base := if m.testBit 9 && m.testBit 4 then 16 else 0
  (selected m).map fun (i,a) =>
    let r := base ^^^ (1 <<< ((hints >>> (4*i)) &&& 15))
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ^^^ (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := (m &&& 511) ^^^ ((m &&& 511) &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
  let xs := supportPairs baseRow s
  let count := (xs.map Prod.fst).toFinset.card
  let drop := colFree free q 0
  let lz := if m.testBit 9 && drop.testBit 4 then drop &&& (511 ^^^ 16) else drop
  let lo := if m.testBit 9 && drop.testBit 4 then 16 else 0
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows lz lo) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
  let xs := supportPairs baseRow s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) _ hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  wires : List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
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
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
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
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
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
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
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
  let x := fun j => if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then (if m.testBit 9 && j.val == 4 then ~~~(v 4) else v j.val) else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · by_cases hf : (m.testBit 9 && j.val == 4) = true
    · have hj4 : j.val = 4 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hf; exact hf.2
      simp only [vertex, hh, hf, ite_true, bit_neg, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]
      exact congrArg Bool.not (asRow_bit v i ⟨4, by decide⟩)
    · simpa [vertex, hh, hf] using asRow_bit v i j
  · simp [vertex, hh, bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
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
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h


def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
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
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh


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
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
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
  exact hi k t hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs,i => xs[i]?
  | .fork pivot a b,i => if i<pivot then a.read i else b.read (i-pivot)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e
    split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)

structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)

def wiresOf (g : Forest) :=
  rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a :=
  raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) := liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val :=
  bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
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

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
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
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def extra3853 (g : Forest) (k tag : Nat) : List (Nat × Nat) :=
  if g.cap=13 && g.mask=383 && k=10 && tag=4441884182832514441 then [(1228,0)] else []

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList ++ (extra3853 g k tag).filterMap (linkedSet g (k-1))
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    rcases List.mem_append.mp hx with h | h
    · have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using h
      obtain ⟨pair,_,v⟩ := Option.bind_eq_some_iff.mp e
      exact linkedSet_sound g _ names (prior (by omega)) v
    · obtain ⟨pair,_,v⟩ := List.mem_filterMap.mp h
      exact linkedSet_sound g _ names (prior (by omega)) v


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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
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
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
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

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl

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

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
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
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList ++ (extra3853 g k tag).filterMap (linkedSet g (k-1))
  (k,ws.length,ws,preCov ws,rules,ls)


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
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
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
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)

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
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (.leaf [])
def g15autos : Array (List Nat) := #[[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i : Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat := 0x2c
def g191d6 (i : Nat) : Nat := 0x47d6448788a00
def g191l6 : Packing := (1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing := (28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing := (100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing := (12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat := 0x1f3c11ff
def g191l10 : Packing := (1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits) := #[(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i : Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing := (25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing := (91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing := (41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing := (6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat := 0x11b280e4ff
def g383l12 : Packing := (1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits) := #[(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1 = true := s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1 = true := s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1 = true := s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1 = true := s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1 = true := s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1 = true := s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact (rfl : block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)
def hashdeadl14 (i : Nat) : Nat := 0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat := 0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat := (if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat := 0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat := 0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat := 0x202e0
abbrev knownPrev_g539 := known383
def g539d3 (i : Nat) : Nat := 0xf
def g539l3 : Packing := (1,0,0,0,0,0,0,g539d3)
def g539samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdffce7fff1c3ff27,0x200a0a0a20914a22),(0xebff073ffe038fc4,0x1510b454d42615c4),(0,0),(0xf33ff8387ffc0cf8,0xca286a669304cb0),(0x83c0003f80000f00,0x7ebbdfff6dbb6fb2),(0,0),(0,0),(0,0),(0,0)]
def g539columns : IndexTree ColumnInfo := (.leaf [])
def g539autos : Array (List Nat) := #[[]]
def g539levels : Nat → Packing
  | 3 => g539l3
  | _ => emptyPacking
def g539index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g539 : Forest := ⟨539,3,fun j => g539samples[j]?.getD (0,0),g539columns,g539autos,g539levels,g539index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg539 : graphValid g539 (boundsBefore knownPrev_g539) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=0)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg539_3_0 : block g539 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg539_3 : block g539 3 0 1=true := sg539_3_0
theorem tablesg539 : checkedTables g539 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g539 0 0 0 = true)
  · exact (rfl : block g539 1 0 0 = true)
  · exact (rfl : block g539 2 0 0 = true)
  · exact allg539_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low539 : Lower (vars 539) (graphGoal 539) 4 :=
  lower_forest (g:=g539) (i:=0) (hints:=16385) (before_sound known383 valid383) geomg539 tablesg539 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps539 : List (Nat × List Nat) := [(539,[]),(541,[118,133,33,48]),(569,[118,130,81]),(793,[82,129,48])]
def known539 := extendKnown known383 4 maps539
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid539 : Known known539 := extendKnown_ok valid383 low539 (by decide +kernel)
abbrev knownPrev_g535 := known539
def g535d3 (i : Nat) : Nat := 0xf
def g535l3 : Packing := (1,0,0,0,0,0,0,g535d3)
def g535samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef9f9ff87e3ff99f,0x1041440c48128912),(0xf7ffe73fffc70fe4,0x8820850928414c4),(0xbbe7f83f8ff80e78,0x451445a54d20aa38),(0,0),(0xc3f8003ff0000f80,0x3e5776fe69b6cf92),(0,0),(0,0),(0,0),(0,0)]
def g535columns : IndexTree ColumnInfo := (.leaf [])
def g535autos : Array (List Nat) := #[[]]
def g535levels : Nat → Packing
  | 3 => g535l3
  | _ => emptyPacking
def g535index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g535 : Forest := ⟨535,3,fun j => g535samples[j]?.getD (0,0),g535columns,g535autos,g535levels,g535index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg535 : graphValid g535 (boundsBefore knownPrev_g535) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=0)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg535_3_0 : block g535 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg535_3 : block g535 3 0 1=true := sg535_3_0
theorem tablesg535 : checkedTables g535 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g535 0 0 0 = true)
  · exact (rfl : block g535 1 0 0 = true)
  · exact (rfl : block g535 2 0 0 = true)
  · exact allg535_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low535 : Lower (vars 535) (graphGoal 535) 4 :=
  lower_forest (g:=g535) (i:=0) (hints:=257) (before_sound known539 valid539) geomg535 tablesg535 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps535 : List (Nat × List Nat) := [(535,[]),(542,[118,133,33,48]),(817,[118,130,81]),(824,[82,129,48])]
def known535 := extendKnown known539 4 maps535
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid535 : Known known535 := extendKnown_ok valid539 low535 (by decide +kernel)
def g606 : Forest := ⟨606,4,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low606 : Lower (vars 606) (graphGoal 606) 5 :=
  lower_discard (g:=g606) (ci:=(0,16,78,0,4)) (hints:=16982304) (before_sound known535 valid535) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps606 : List (Nat × List Nat) := [(606,[]),(663,[118,133,33,48]),(881,[82,129,48]),(952,[118,130,81])]
def known606 := extendKnown known535 5 maps606
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid606 : Known known606 := extendKnown_ok valid535 low606 (by decide +kernel)
def g693 : Forest := ⟨693,4,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low693 : Lower (vars 693) (graphGoal 693) 5 :=
  lower_discard (g:=g693) (ci:=(0,16,165,0,4)) (hints:=536872708) (before_sound known606 valid606) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps693 : List (Nat × List Nat) := [(693,[]),(700,[82,129,48]),(851,[118,130,81]),(858,[118,133,33,48])]
def known693 := extendKnown known606 5 maps693
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid693 : Known known693 := extendKnown_ok valid606 low693 (by decide +kernel)
def g627 : Forest := ⟨627,4,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low627 : Lower (vars 627) (graphGoal 627) 5 :=
  lower_discard (g:=g627) (ci:=(0,16,99,0,4)) (hints:=16777217) (before_sound known693 valid693) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps627 : List (Nat × List Nat) := [(627,[]),(691,[118,130,81]),(860,[82,129,48])]
def known627 := extendKnown known693 5 maps627
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid627 : Known known627 := extendKnown_ok valid693 low627 (by decide +kernel)
def g573 : Forest := ⟨573,4,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low573 : Lower (vars 573) (graphGoal 573) 5 :=
  lower_discard (g:=g573) (ci:=(4,0,569,0,4)) (hints:=8964) (before_sound known627 valid627) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps573 : List (Nat × List Nat) := [(573,[])]
def known573 := extendKnown known627 5 maps573
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid573 : Known known573 := extendKnown_ok valid627 low573 (by decide +kernel)
def g567 : Forest := ⟨567,4,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low567 : Lower (vars 567) (graphGoal 567) 5 :=
  lower_discard (g:=g567) (ci:=(0,16,39,0,4)) (hints:=257) (before_sound known573 valid573) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps567 : List (Nat × List Nat) := [(567,[]),(798,[118,133,33,48]),(828,[82,129,48])]
def known567 := extendKnown known573 5 maps567
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid567 : Known known567 := extendKnown_ok valid573 low567 (by decide +kernel)
abbrev knownPrev_g543 := known567
def keyg543l6 (i : Nat) : Nat := 0xa00b508000738000000
def g543d5 (i : Nat) : Nat := 0xa50be44f611fa00
def g543l5 : Packing := (3,1,0,0,0,4,0,g543d5)
def g543d6 (i : Nat) : Nat := 0x3f
def g543l6 : Packing := (1,0,0,0,0,0,0,g543d6)
def g543samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed4defc739b9f071fe3fc3c1e3e3c7ff1c1f83e38e3838ffece621f,0x12a010b062520c0510830098510494600584a1830412204b0ca4212),(0x77b1fff83e3e6f81fffffc01fc03f8f8e01ffffc0fc03f1c10fec64,0x884a010580a090c86204482282292181220946340a844a103052c44),(0xb9fe77ffc03f8ffe3fc7fffe0003ff00ffe3fc1ff0003fe01f39078,0x46010a102d402511041191080552102a48a22889a000b4814a29038),(0xfe3f87ffffc00fffc007fffffffc0000fffc001fffffc0001fc1f80,0x1c054240035584031262231120024c4931043124d26000215c0b00),(0xc03ff80000000ffffff8000000000000ffffffe0000000001ffe000,0x3fe957bef7fffe6db9b73bbddb9fbef7ffdff3d36db726db9ffeb12),(0,0),(0,0),(0,0),(0,0)]
def g543columns : IndexTree ColumnInfo := (.leaf [(0,16,15,0,4)])
def g543autos : Array (List Nat) := #[[],[33,48]]
def g543levels : Nat → Packing
  | 5 => g543l5
  | 6 => g543l6
  | _ => emptyPacking
def g543index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 4 11 4 7 2 1 (keyg543l6)
  | _ => fun _ => none
def g543 : Forest := ⟨543,6,fun j => g543samples[j]?.getD (0,0),g543columns,g543autos,g543levels,g543index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg543 : graphValid g543 (boundsBefore knownPrev_g543) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=0)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg543_5_0 : block g543 5 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg543_5 : block g543 5 0 3=true := sg543_5_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg543_6_0 : block g543 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg543_6 : block g543 6 0 1=true := sg543_6_0
theorem tablesg543 : checkedTables g543 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g543 0 0 0 = true)
  · exact (rfl : block g543 1 0 0 = true)
  · exact (rfl : block g543 2 0 0 = true)
  · exact (rfl : block g543 3 0 0 = true)
  · exact (rfl : block g543 4 0 0 = true)
  · exact allg543_5
  · exact allg543_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low543 : Lower (vars 543) (graphGoal 543) 7 :=
  lower_forest (g:=g543) (i:=0) (hints:=8449) (before_sound known567 valid567) geomg543 tablesg543 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps543 : List (Nat × List Nat) := [(543,[]),(825,[118,130,81])]
def known543 := extendKnown known567 7 maps543
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid543 : Known known543 := extendKnown_ok valid567 low543 (by decide +kernel)
def g631 : Forest := ⟨631,5,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low631 : Lower (vars 631) (graphGoal 631) 6 :=
  lower_discard (g:=g631) (ci:=(4,0,627,0,5)) (hints:=16777473) (before_sound known543 valid543) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps631 : List (Nat × List Nat) := [(631,[]),(892,[82,129,48]),(926,[118,133,33,48])]
def known631 := extendKnown known543 6 maps631
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid631 : Known known631 := extendKnown_ok valid543 low631 (by decide +kernel)
abbrev knownPrev_g755 := known631
def g755d6 (i : Nat) : Nat := 0x7f
def g755l6 : Packing := (1,0,0,0,0,0,0,g755d6)
def g755samples : Array (Bits × Bits) := #[(0xbdc3c79cfe37f9fe3fbfffe003f800fe07c0fe3fc1fe1fffe07ffc1fff1fe1ffffffffffe0001fc0007f01f80ff007e07fc03ffffc07ff81fffc01ff00ffffffffffffffe007001c1f078060e03fff83f83fc0380ffffffffffe10c81f330fff,0x4218102209480409404040028013020540220120902120401102084800841208009200400a00092048148012008812004088088440820801088205020840a20052101420100404100a0490008022910220124420088680260542108812210912),(0xf6dc0fe33fc7e63fc7ce79e0fc001ffff83f003ffe001ffc1f83ffe07ffffe0fc1fc0ffe001fe0007ffffe07f00007ff80003ffe03f81ffe03ffffffff01fc07e01fffc0007807ffe0f8007f003fe07c1fc3fffff03c0e0ffe001f319ccdf25c,0x923620c401009501830821c0924a41824404c41008a421062189102920880b213005000b088a00902a10c80144264a109114518850882a41114484c4403043480a4a104602800a520582275048d220c0940914a60184a4978040a318c88a24c),(0,0),(0,0),(0x28a00803c00707c0060f819f00001f00003fffc000001f001ffc00007fe0000ffe000f801fe000007f800007fffff80000003f0003ffe00003fffe000001fff8001fc0001f8007e000ffff80003e007fe003ffc0003ff00fc0039c3e18f1c398,0xd75fb6f63bfc7d3be9f85e66fad7caadeea6152bbbedecd5b52a7b7b249dbf5cb1b6ba57faba9b365b74d536add8b68b52bdaeadcb96ba1d6bda9516ddd5eb51d6db3569b584a5731aaff69489379536e533fda0a9afd8af8d4b9cbe1af1cb9a),(0xcffff003fff807fff80ffe1fffffe000003fffffffffe0001fffffff8000000ffffff0001fffffff80000007ffffffffffffc00003fffffffc0000000001ffffffe000001ffff80000ffffffffc0007ffffc0000003ffff00003e03fe0fe03e0,0x30010f581005b800029000a810609c50b30828060848061ac01020020e21c4610020028a60c2c24312002840c16140c6070504101020d30830503828161850a304818182c299280000310726238000595da4090142316dc11011402540de02e0),(0xf3ffffc000007fffff0001fffffffffffc00000000000001ffffffffffffff0000000001ffffffffffffff8000000000000000003fffffffffffffffffe0000000000001fffffffff0000000000007fffffffffffc000000003ffc000fffc00,0xf0c80403bdaed021000b6de0a0811060c23cb1b42d7198e31843425048111009a43b2b6d431313a41c46b064898d8014642628c162c51c51c26321b0989062c2071206331b57b65a5304440012201863963b2e358f0181020063f5c000775c00),(0xf03ffffffffff8000000001fffffffffffffffffffffffffe000000000000000000000001ffffffffffffffffffffffffffffffffc0000000000000000000000000000001fffffffffffffffffffff8000000000000000000003ffffff000000,0xfd20000210007bdb56df750c30600810430c038318110801e63839c70de198e39c3cc719c1c1c386078c1870e0e0718783830e1830600618383c1c0e0e18304181c383c1c66c79f9cc67858dc39de02000230060c02000c2182bfdabf000000),(0,0)]
def g755columns : IndexTree ColumnInfo := (.leaf [(0,16,227,0,5)])
def g755autos : Array (List Nat) := #[[],[118,81]]
def g755levels : Nat → Packing
  | 6 => g755l6
  | _ => emptyPacking
def g755index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g755 : Forest := ⟨755,6,fun j => g755samples[j]?.getD (0,0),g755columns,g755autos,g755levels,g755index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg755 : graphValid g755 (boundsBefore knownPrev_g755) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=0)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg755_6_0 : block g755 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg755_6 : block g755 6 0 1=true := sg755_6_0
theorem tablesg755 : checkedTables g755 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g755 0 0 0 = true)
  · exact (rfl : block g755 1 0 0 = true)
  · exact (rfl : block g755 2 0 0 = true)
  · exact (rfl : block g755 3 0 0 = true)
  · exact (rfl : block g755 4 0 0 = true)
  · exact (rfl : block g755 5 0 0 = true)
  · exact allg755_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low755 : Lower (vars 755) (graphGoal 755) 7 :=
  lower_forest (g:=g755) (i:=0) (hints:=1358954497) (before_sound known631 valid631) geomg755 tablesg755 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps755 : List (Nat × List Nat) := [(755,[]),(988,[118,133,33,48])]
def known755 := extendKnown known631 7 maps755
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid755 : Known known755 := extendKnown_ok valid631 low755 (by decide +kernel)
abbrev knownPrev_g727 := known755
def g727d6 (i : Nat) : Nat := 0x7f
def g727l6 : Packing := (1,0,0,0,0,0,0,g727d6)
def g727samples : Array (Bits × Bits) := #[(0x6e01cf19ff86f9fc7cf3f1e0001f81fc1f80fc7ffe07f07ff03f0ff03ffe0ffc1ffe0ffff000003fc07f03f807f007ff81ff00fffc03fc01f80fffe03fff80fffc0ffffff0000f0707c3e01f8781ff83e030ff03ff81ff07ffff206cc7a3399f,0x915c14a402698412830886052a01388a8452022244908ca90880a821904950814048582405490012a41480924049118a01122488a0a09224a108a4411214129088290a9109100a040282a49105009143222054029490e4048aa3204c82a22912),(0xf77e0fe67ff8f7ff8f7ffe61ffe001ffe07f007ffff8007e0fffffffc1fff0fffffff03f800fffc0007ffc07f80007fffe0000fc03fffffffff03fffc03ffffffff01fe0001ff007f83c001ff801e07fffff07fc07fffff83c003990e4fccfe4,0x8816008800200203080009800484210108048800802110011080244028005200080014028002840082109000a02203084204111050504400a2008880060a021120030021002a00148140806c8112204484101480143099030041110641084c4),(0xbf9ff0078fff067ff07cff9e0ffffe00007fff83ffffff800fc00ffffe0000ffe0ffffc00ff01fffff800007fffff81fffffff0003fc0001ffffc000003fff01ffffe0000fe07ff8003fffe0fffe007c003ff80007fe07ffc003c61f38c70e78,0x40640dd05420b88005010021c28208a12d1410287051040b60063080801a62080510400590520284c50010a0d0914083181c1400282850393141050246891414e0a200a1616013280008c1a0118c0059043a9810a6342667002a840a10c70a38),(0,0),(0x4e00007f0000780007f001ff0000000007ffffc000000000ffff000000000ffff0000000fffe00000000007ffffffe00000000003fffffe00000000003ffffe000000000fff8000003fffff0000007fffc0000007fff8000003f81fc0f80f80,0xfb5fbefc4effdc77dfc8bfed6fd77ddbde5a2a3adddfafedba92a9edf5ddfbd354dafaeefd6b5a36b774ead6e6e9b5da2d56f6bbb3b3daada1eba6dbb73e5adcbabb5ad5bbb58aa4c6affddb4525956ffea8d42ad7f9f4359ab3f85fc2fa2f92),(0,0),(0x38fffff8000007ffff80001fffffffffff800000000000000fffffffffffff00000000000ffffffffffffff8000000000000000003ffffffffffffffffc00000000000000fffffffffc000000000007ffffffffff80000000003ffe000fff000,0xc70808876f75e842005fdb618b0410e1887cb3736165ce71cc240d092111409a761d6cb7518393272646b0e484cdc500519898c2c2c26331c58e3713240c1c98c0c38319cdd95fb694c2911000481873973ce6b3e420404600c3eee000ef7000),(0xc0fffffffffff8000000001ffffffffffffffffffffffffff000000000000000000000000ffffffffffffffffffffffffffffffffc0000000000000000000000000000000fffffffffffffffffffff8000000000000000000003ffffff000000,0x3f1100000840077b6aeeedd00c1861021060c043818608400f38ce0e39e18ce398e18f386e0c1c383878c307070e061c61e0e0e3030383c0060c381c383060e1030c1c1e0e1e6cc7e7331e1ce671de02180000c30041808023017bf5ef000000),(0,0)]
def g727columns : IndexTree ColumnInfo := (.leaf [(16,0,198,1,5)])
def g727autos : Array (List Nat) := #[[]]
def g727levels : Nat → Packing
  | 6 => g727l6
  | _ => emptyPacking
def g727index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g727 : Forest := ⟨727,6,fun j => g727samples[j]?.getD (0,0),g727columns,g727autos,g727levels,g727index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg727 : graphValid g727 (boundsBefore knownPrev_g727) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=0)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg727_6_0 : block g727 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg727_6 : block g727 6 0 1=true := sg727_6_0
theorem tablesg727 : checkedTables g727 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g727 0 0 0 = true)
  · exact (rfl : block g727 1 0 0 = true)
  · exact (rfl : block g727 2 0 0 = true)
  · exact (rfl : block g727 3 0 0 = true)
  · exact (rfl : block g727 4 0 0 = true)
  · exact (rfl : block g727 5 0 0 = true)
  · exact allg727_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low727 : Lower (vars 727) (graphGoal 727) 7 :=
  lower_forest (g:=g727) (i:=0) (hints:=553648385) (before_sound known755 valid755) geomg727 tablesg727 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps727 : List (Nat × List Nat) := [(727,[]),(734,[118,133,33,48]),(1009,[118,130,81]),(1016,[82,129,48])]
def known727 := extendKnown known755 7 maps727
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid727 : Known known727 := extendKnown_ok valid755 low727 (by decide +kernel)
abbrev knownPrev_g702 := known727
def g702d6 (i : Nat) : Nat := 0x7f
def g702l6 : Packing := (1,0,0,0,0,0,0,g702d6)
def g702samples : Array (Bits × Bits) := #[(0,0),(0x650839e1867c39c0fc37cce000f000fc07f03f001f83fc07c0fc00fff03f07ff07ff80f1f0001fe0003fc01fc0fe0003fc07e03f01fc003fff03f807ffe03ffff00ff007f007f007870f801f031f07801ff0f81ff81ff87f00ff18ca649b39b3,0x9a77425a6992c31d12cc33157a0b680acd2544ce522d4a2a252ab6a62350ac92a8225b0b494900bd2012ec9254a493106712b41a9329152495a310ce4934ac9d20548b2caa05b447850aa515430ba4a212d05c89c896687a09ab18ca64932932),(0xbf37c1fe3fffc1ffffc7ff607f01ff0007ffc007fffffff800ffffffffc007ffffffff01f01fe0000fc0001fff0001ffffffffc001fffffffffc0007fffffffffff00007f078000807f001ffffe007ffffff001fffffff8000fc210f87fc3fc3,0x40882c0080201c000010008a00a4022110400910840090804a40000040051004000400340200220241400104820824248840428004508041220841108241010241001051001800880250082214200118a52501121128950002502101024c14c1),(0xcec7fe00387ffe073ff8ff9f8001fffff8000007e003ffffff001f07fffff83ff87ffffe0fe000000fffffe0000001fc0007fffffe000fc07ffffff81fffc01ffffffff80f80000ff80001e003fff803e07fffe0ffe03fffff03c00c78e7ce7c,0x312101dd45420168a205006054492410450a34e211492124208a50948920818005484801505214948a24a44000a14052222491145102091444922442141424548a4909002a848905500001508292900250489440e6822254a803c00c50a28a28),(0x8f800003f800007c000f01ffffe000000000007fffc000000001ff80000003fff8000000ffffffff0000000000001fffff8000000000fff800000001fffffe0000000000ffffff0000001fffc000003ff800000ffffc0000003fe0f80f80f80,0xf727b7ffe5776ffcb77f0fe35669b6dbe7efbefb596b3bb6b3ef7ad5ebb6dde8a56eeddffb7b56d4eb36b6562af5f97af2b699b6d99badb674dab5e3df9eb654eb6dad9dbfeeddd5504a51fbda9ad44b79ccd658ffdf2356ac1bfe0fd0fa8fa8),(0xfffffffc0000007ffff001ffffffffffffffff80000000000001fffffffffc0000000000ffffffffffffffffffffe000000000000000fffffffffffe0000000000000000ffffffffffffe0000000003ffffffff000000000003fff000fff000,0xf002208837fbb7b0000055ac18803861818318439e71c1c73c7184010204010e318f0e6663838707038707870c387060c0c002186060c61878e0c183070707870381c1e1c330e1e99b631c00100000139e7ee79c430c04183062b5a000fff000),(0,0),(0xf0fffffffffffff80000001fffffffffffffffffffffffffffffe00000000000000000000ffffffffffffffffffffffffffffffffffff0000000000000000000000000000ffffffffffffffffffffffc00000000000000000003ffffff000000,0xf04011000000006fbaeaa506001c082060c208400020200008218e60c38e630c67070898c1c18180c38381830c1818303071c208183082000030604181838180c0e0e060c470e06648c619ce3dce6600000000084100060c0814a5efd000000),(0,0)]
def g702columns : IndexTree ColumnInfo := (.leaf [(0,16,174,0,5)])
def g702autos : Array (List Nat) := #[[]]
def g702levels : Nat → Packing
  | 6 => g702l6
  | _ => emptyPacking
def g702index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g702 : Forest := ⟨702,6,fun j => g702samples[j]?.getD (0,0),g702columns,g702autos,g702levels,g702index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg702 : graphValid g702 (boundsBefore knownPrev_g702) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=0)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg702_6_0 : block g702 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg702_6 : block g702 6 0 1=true := sg702_6_0
theorem tablesg702 : checkedTables g702 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g702 0 0 0 = true)
  · exact (rfl : block g702 1 0 0 = true)
  · exact (rfl : block g702 2 0 0 = true)
  · exact (rfl : block g702 3 0 0 = true)
  · exact (rfl : block g702 4 0 0 = true)
  · exact (rfl : block g702 5 0 0 = true)
  · exact allg702_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low702 : Lower (vars 702) (graphGoal 702) 7 :=
  lower_forest (g:=g702) (i:=0) (hints:=544416032) (before_sound known727 valid727) geomg702 tablesg702 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps702 : List (Nat × List Nat) := [(702,[]),(890,[118,130,81]),(949,[82,129,48])]
def known702 := extendKnown known727 7 maps702
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid702 : Known known702 := extendKnown_ok valid727 low702 (by decide +kernel)
def g695 : Forest := ⟨695,7,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low695 : Lower (vars 695) (graphGoal 695) 8 :=
  lower_discard (g:=g695) (ci:=(0,16,167,0,7)) (hints:=536871169) (before_sound known702 valid702) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps695 : List (Nat × List Nat) := [(695,[]),(862,[118,133,33,48]),(883,[118,130,81]),(956,[82,129,48])]
def known695 := extendKnown known702 8 maps695
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid695 : Known known695 := extendKnown_ok valid702 low695 (by decide +kernel)
abbrev knownPrev_g701 := known695
def keyg701l7 (i : Nat) : Nat := 0x130939a60200000d4000020
def g701d6 (i : Nat) : Nat := 0x7a8a0bf2af78cfec23fa00
def g701l6 : Packing := (4,1,0,0,0,5,0,g701d6)
def g701d7 (i : Nat) : Nat := 0x7f
def g701l7 : Packing := (1,0,0,0,0,0,0,g701d7)
def g701samples : Array (Bits × Bits) := #[(0xffffffffffffffff57a21e78c7e7333fc67fb807803f07e0fe01e3f01f0f8787fffc1fc3ffe3f878fe0007f8007e07e1f8001f81f81e07e07e07fffff87e07fffe07e01fe07ff80780421c03c047878787fff870fff01c3c07ff882c867e3c4f,0xa855c8953008448129c041506802a44a19240428c41148504088c92650110485811220344023044112118244b40524491862524030442146211440c890c50404a04010225242c505048c601022919828214c882c84540c4a),(0,0),(0x9de5e07f0ff83ccff877d8780fc007ff001fffffe00ff87878ffe003e1ffff80f007f8001f8007fe001fffffffe007ff81f81f81ff8007807fffffe0007e00780083e03ffff807f878780f80f0ffffc00780113f19992f8c,0x621a5b005083c11002802605308848822a48814245640283011043480240201b024028928280216420a2a490194009850a29409499104a0a8a228240a31028180482a084868801b028312a84b422ae800e05110a11192a8c),(0xe6d9ff8009ffc0f3ff87e7800ffff800001e03fffff0007f80fffffc01ffffff01f800001ffff800001fe001fffff80001ffe001fffff8007fffffffff80078000fc003c007ff8007f800fff00fffffff800e030e1e1cff0,0x19248076a5001e0a2058186249042414d18054849009514054a29020d40244009c148525144b1001050512492488a41051440a492249201451051492100514844868002a2064d0041502445200cd1132a008e030c0e08560),(0x1e00000e0000fc000607fff0000000001ffc000000007fff00000001fc000001ffffffe0000000001ffffe0000000001fffffe000000007ff80000000007ffff00003fff8000007ffff00000ffe0000000fe3f01fe0f00,0xfff5fdfff5bdff8b7ff9fb736fb6f7dffdf556eef6bdfdf574fafbbeff936fefff5eb5bdd66bd55dd7d7d76db6ddb6dddd777b6db76d775f7dd5d6faddd7dfefed68933ff766f5575fdf765aaaffd9bab34efe3fc5fe8f6a),(0xf8fffffff00000fffff807ffffffffffffe000000000007ffffffffffe00000001ffffffffffffffffe000000000000001ffffffffffffff80000000000007ffffffffc0000000007fffffffff0000000000ffc001fff000,0x70010200fd6ab000002ac04021841046019990718c626020040020080c471322660c1c2070c6188618604300100c10620818c11c430441818620703061861310e8ec5800400002062638f6ccc060200c410558001abf000),(0,0),(0xff1fffffffffff00000007ffffffffffffffffffffffff80000000000000000001fffffffffffffffffffffffffffffffe0000000000000000000000000007ffffffffffffffffff80000000000000000000fffffe000000,0xe10044000000efb56d50400c208618810002080008406466831c33191b8644c98706041871861186181841c611061841061060004180606184181c1861864670711a333877664604040000008800230060aa75ee000000),(0,0)]
def g701columns : IndexTree ColumnInfo := (.leaf [(0,16,173,0,5)])
def g701autos : Array (List Nat) := #[[],[82,48]]
def g701levels : Nat → Packing
  | 6 => g701l6
  | 7 => g701l7
  | _ => emptyPacking
def g701index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 3 11 4 7 2 1 (keyg701l7)
  | _ => fun _ => none
def g701 : Forest := ⟨701,7,fun j => g701samples[j]?.getD (0,0),g701columns,g701autos,g701levels,g701index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg701 : graphValid g701 (boundsBefore knownPrev_g701) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=0)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg701_6_0 : block g701 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg701_6 : block g701 6 0 4=true := sg701_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg701_7_0 : block g701 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg701_7 : block g701 7 0 1=true := sg701_7_0
theorem tablesg701 : checkedTables g701 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g701 0 0 0 = true)
  · exact (rfl : block g701 1 0 0 = true)
  · exact (rfl : block g701 2 0 0 = true)
  · exact (rfl : block g701 3 0 0 = true)
  · exact (rfl : block g701 4 0 0 = true)
  · exact (rfl : block g701 5 0 0 = true)
  · exact allg701_6
  · exact allg701_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low701 : Lower (vars 701) (graphGoal 701) 8 :=
  lower_forest (g:=g701) (i:=0) (hints:=536879876) (before_sound known695 valid695) geomg701 tablesg701 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps701 : List (Nat × List Nat) := [(701,[]),(859,[118,130,81])]
def known701 := extendKnown known695 8 maps701
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid701 : Known known701 := extendKnown_ok valid695 low701 (by decide +kernel)
def g607 : Forest := ⟨607,7,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low607 : Lower (vars 607) (graphGoal 607) 8 :=
  lower_discard (g:=g607) (ci:=(64,0,543,0,7)) (hints:=16785665) (before_sound known701 valid701) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps607 : List (Nat × List Nat) := [(607,[]),(671,[118,133,33,48]),(889,[82,129,48]),(953,[118,130,81])]
def known607 := extendKnown known701 8 maps607
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid607 : Known known607 := extendKnown_ok valid701 low607 (by decide +kernel)
def g575 : Forest := ⟨575,7,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low575 : Lower (vars 575) (graphGoal 575) 8 :=
  lower_discard (g:=g575) (ci:=(32,0,543,0,7)) (hints:=8449) (before_sound known607 valid607) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps575 : List (Nat × List Nat) := [(575,[]),(829,[82,129,48])]
def known575 := extendKnown known607 8 maps575
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid575 : Known known575 := extendKnown_ok valid607 low575 (by decide +kernel)
def g763 : Forest := ⟨763,7,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low763 : Lower (vars 763) (graphGoal 763) 8 :=
  lower_discard (g:=g763) (ci:=(8,0,755,0,7)) (hints:=1358970881) (before_sound known575 valid575) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps763 : List (Nat × List Nat) := [(763,[])]
def known763 := extendKnown known575 8 maps763
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid763 : Known known763 := extendKnown_ok valid575 low763 (by decide +kernel)
def g766 : Forest := ⟨766,7,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low766 : Lower (vars 766) (graphGoal 766) 8 :=
  lower_discard (g:=g766) (ci:=(32,0,734,0,7)) (hints:=561193248) (before_sound known763 valid763) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps766 : List (Nat × List Nat) := [(766,[]),(983,[118,133,33,48]),(1013,[82,129,48]),(1018,[118,130,81])]
def known766 := extendKnown known763 8 maps766
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid766 : Known known766 := extendKnown_ok valid763 low766 (by decide +kernel)
def g639 : Forest := ⟨639,8,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low639 : Lower (vars 639) (graphGoal 639) 9 :=
  lower_discard (g:=g639) (ci:=(32,0,607,0,8)) (hints:=16785665) (before_sound known766 valid766) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps639 : List (Nat × List Nat) := [(639,[]),(893,[82,129,48]),(927,[118,133,33,48])]
def known639 := extendKnown known766 9 maps639
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid639 : Known known639 := extendKnown_ok valid766 low639 (by decide +kernel)
def g735 : Forest := ⟨735,8,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low735 : Lower (vars 735) (graphGoal 735) 9 :=
  lower_discard (g:=g735) (ci:=(128,0,607,0,8)) (hints:=553656577) (before_sound known639 valid639) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps735 : List (Nat × List Nat) := [(735,[]),(1017,[118,130,81])]
def known735 := extendKnown known639 9 maps735
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid735 : Known known735 := extendKnown_ok valid639 low735 (by decide +kernel)
def g759 : Forest := ⟨759,8,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low759 : Lower (vars 759) (graphGoal 759) 9 :=
  lower_discard (g:=g759) (ci:=(0,16,231,0,8)) (hints:=553648385) (before_sound known735 valid735) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps759 : List (Nat × List Nat) := [(759,[]),(990,[118,133,33,48]),(1011,[118,130,81]),(1020,[82,129,48])]
def known759 := extendKnown known735 9 maps759
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid759 : Known known759 := extendKnown_ok valid735 low759 (by decide +kernel)
def g887 : Forest := ⟨887,8,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low887 : Lower (vars 887) (graphGoal 887) 9 :=
  lower_discard (g:=g887) (ci:=(4,0,883,0,8)) (hints:=21491613953) (before_sound known759 valid759) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps887 : List (Nat × List Nat) := [(887,[]),(894,[82,129,48]),(958,[118,133,33,48])]
def known887 := extendKnown known759 9 maps887
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid887 : Known known887 := extendKnown_ok valid759 low887 (by decide +kernel)
abbrev knownPrev_g703 := known887
def keyg703l7 (i : Nat) : Nat := 0x14680039000000000
def keyg703l8 (i : Nat) : Nat := 0xb8d156525b9aa7c65a7647030c8b9480dd9bc109fa2c05c83361e9400000124593b3792b504d255521f8f4b60012a02780000067110a890000000000070af041d60366e00180e08047b31689029a8a7c00386c68448000499620038a800a2da004bfbe000111539b50010ed613ad44a11608a1a2640bf0ec8e015cf005d400010f765e902668e2d33b09a043f55873400101262c20000046032818007060428048092001608000
def keyg703l9 (i : Nat) : Nat := 0x5d99fa943971c10a07d3a684510c16324c79680ee349bdaf5bdd9100d5782d5a888cf8e18721245177540000000000000006a04f5d60420d3017c6bfd972b8000000474f019b8000cfc0000c6027c96f4a49000018701a75fe9ba7fd1c00000000086c00000350e88dedaefc00358363264365c00000000210018d428000001200d2b66aaae0c0002f37068000000694ee80025c1ca840773912c1b0a14b066dca5be4b0869a483b61d93c0028cab500029a8d9891800229374c2b18d4c7f43f657809c568ee4b0451222358d66e521e7150000000000a3c0023651c8740003de15e8000dfc000ab72c321b2340005b400024771ae0f481834558e0bb3ce2a8f000000326c00346400084800000132c001cfb84668e211da372330c5de315b1201c69c94ea7aaf82276f4733c4e48a6cc9551c5d9e8585d2ce9ad1b4758a8ba0aec62905b0967432baa9cbd2ed4d0534e4d49d50a1226e4ca366622caa5273401f1c16b2f32388da16f2c58e642c5f62c9c4114bdf11770a545d9efa601cdf624b48de4319465d4d5c18100000408030b80402020d8001801020f41000008006c0b0009040000482c0c05020000209060000605028001600080000a0f0202c1007000440202158147e00010040a08058001606298002c1b0007c5203
def keyg703l10 (i : Nat) : Nat := 0x1e2233dfa7f245547c78900000018e7800001ad004d49e007b59648000458431d4fc8000087a580058e00041400041c0000
def g703d6 (i : Nat) : Nat := 0x14a12bd69a215291267ab3442c1224ed4668848244
def g703l6 : Packing := (3,4,4,0,0,4,0,g703d6)
def g703d7 (i : Nat) : Nat := 0xa84a0498400281000054202a10532820140b5282000984a049840000099411528200000000000000000000000000010000000000cc1cc1cc10520800870800e60e60e60e6080004200210010801482042000000021a7a92a1a819f2709ae6698655942448fe2c89e1b822037f9f2799da755d072dc66cda066d966458c61d825f5785cd6e5a56457d5a5555052d465053c4c12b49921471174490d420fc3c0e437cd331cbb2bca325c8b1fc7a1d4691905814c471083d0c4250801b0581103000fb96048244fad2148244fad5248244bbe8858a44bbe8854a44ebd6258644bbe8858644bbe8854244bbe8854644fb56148644bbd6848644bbd5848644bbe8848644ebd6158244bbe8858244f3d5154244f3d5254644bbd2844244bbd5844244bbd6844244fb92044244fb55144244bbd5808244bbd6808244bbe8848244fb41848244bbd6848244bbd5848244f365591211eb666912119f47848211bb4484c211f4e558ce22ece668ce22eae6691222fe22284600fb24484600f725584600ef26684600fca3388a00faa4488a00f6a5588a00eea6688a00f5a558ce00eda668ce00f2e5591222eba6691200b795809e0097d5809e00bb8484c200fc63388a11fa64488a11f665588a11ee66688a11f56558ce11ed6668ce11f3a559120097d5809d639f51809d639f90809d638fd689dd529dd3811d6197d5809d619dd3809d619f90809d619ec2859d318fd6809d3197d5809d319f90809d3197d589dd60fd233846009bc4855d309be8811d309bc484dd209f5189dd209bc484dd10abc484c266b3c484c2559dd3811e229bc4841e22bac484c222bcd3811e22bac4841e22aed6801e22bcd3801e229bc4859d30
def g703l7 : Packing := (86,3,4,0,0,10,0,g703d7)
def g703d8 (i : Nat) : Nat := (if i<1 then 0xb7db69b3db29b15b01aedad9ac5ab1a85a71a5da49a35a21a0d9f99e59d19a599196595193d9298fd8e98d58a989588186d8598458318057f17ad7817557296e56b968d66164d6215f55b159d5595154e94a549146543940d3f93b538935d3313052d92ad28126d2412152011d51a917d16913d0f90cd08905d031004f90f7cf38f0ceb0e84e70e5ce30e04dd8dacd80d6cd40d14d00cbcca8c94c80c6cc58c44c30c04bf0bdcbc8bb4b70b44b18aecac0a94a68a3c9f89b497092c9008d48a88648207f47b079c7887747486ec69061c5c059455050c4b043c3c83542f82b42581fc1a01440d005c003f6b1445fb54a22fd885117ed3288bf690c45fb48222fd841115fd6788afeabc457f11e22bfa6f1177d21956fe83c45bf99a22efcab117be4488bef19c45fb58e22fdaa7117ed6188bf6a8c45fb4c622fdac1117ed5088afe8bc45df10255efa612af7d20957be104abdf44255f7ac5227bd52913deb0c89ef54644f7a43227bd60913ee88467ef48244f7841227bd10913eeb1467f754a33fbac319fdd518cfee90c67f758233fbaa119fdd208cfee10467ef54244ff261007f920803fc884017f11e00bf84f006fe66803bf2ac01ef91200fbc67007ee22803fb08c01fb10222ff2a7007f962803fca9401fe10a00ff265007f961803fca8c01fe4c600ff243007f847803fc13c01fe88a00ff2c7007ed3088bf688445fb59e22fdaaf117ec4788bf69bc45fb45e22fda0f117ec0788bf73bc45fd58e11ff2a1007f562847faa9423fd10a11fea6508ff560847faa8423fd10211fea6108ff520847fa10423fd88a11ff2c1007f553847ee99263fd54531bface98dfd574c6fe13a637f9dd31feac290ff531486feb3a437f55d21bf88e90dfd27102ff3ba43bf58d60dfac2b05fc47582fe13ac17f9dd60efaa2a85fc47542fe13aa17f9dd50bface205fd57102fe9ba437f9dd63bf84ea9dfe7754f7eb1ac57f11d62bfceeb177d5354afe23aa57f9dd52bface215fd5710afe8b8857f9dd51bfcee217dd634cafeb3a657f55d32bfcee996fd62586fe23ac37f09d61bfceeb0f7d52546fe23aa37f09d51bfa0e215fd67082feab8417f4dc20bfa2e107f551443fc902217f59d10bfaae885fc47442fe9ba217f49d10bf84e887f9200837e214cdbf4ca66dfa63336fd2199b7e204cdbf4c266dfa41336fc2099b7e884cddf10a55efa652adfc2758eff3ba217f09d30bfcee987ed52483f6212417f55d30bfa2e205fd674c3ee98a61f754d30fbac6987ed21483fcb0241ef11d30bface905fd57482fe23a417f4dd20efa632aff417482ff3ba41fe4c120df4cd0077a55803dd22401f68ce00fe423007ea22802de23a61bb99a22f5c89116be669139f2ac89f38ce22fcc4508fd633847db22423dd95611deccd08ede668cfaf2ac67db95622 else 0x2a10000a04000400a4158200c010012c72014a411c00000004c200020028100184e66d4662090c2b336a3310485184e6019882428c2b300cc412154e66d98823b09cc029104702a9ccda9104798a89924c5080a840002610281030acc02910470281024108010012c605322411c000000054200000000120800000000001308120800054200261000000013080418530660cc112614c1142b040285208910811ac28c4124114010040a4100200e2144158330660cc15829040b05208220c41882088228c29822cc2982205208810a0100a88248220400e20800b04a086110218409056080400400000000140800000b308a0cc198218520cc18821cc21061063085184204508e10c410a2092088b080002c1624506c48a0d64a4508b48a0d40c8a0ab044c48a0d64a4508c4caa846264d422d228390412d20835a4106c4820d89041b1348a1189a4508c48a0e98695a94693291e8f28de8b288685a82e81a7d67c27ae6f26de6ca6b66a268e67a64e63a60e5fa5e65ba5a65924be3ea3162421860ca0b5ff9f85f41f2df01eeded9ec5e99e85e59e45d89d75d49d35d09cc5cb1c9dbe1bcdbb9ba5b91)
def g703l8 : Packing := (218,2,4,0,0,12,0,g703d8)
def g703d9 (i : Nat) : Nat := 0xa35a4923567ba146b2264a28d7221649124a35924628c865956440e45591122146b4c886225065948940ccb32c89448ab22503918a3224c528c8932ccb4a2442ad281c886324451a4cb21b159cb744910896e8521912dd064362b3350443e2b3351643e2b396e843e2b396c86d0f0cbbadfaf29ea02679122680de5709a46056350131438e12f89b1cc4b08c00ff803fe22ff443fc20ff483fd30ff543fd60ff487fd63ff54ffd62ff54bfc42ff4cbfd61ff547fc40ff4c7fa00bf99b7e55ef913de33fb88bf611
def g703l9 : Packing := (26,1,4,0,0,10,0,g703d9)
def g703d10 (i : Nat) : Nat := 0x8532b437f
def g703l10 : Packing := (1,0,4,0,0,0,0,g703d10)
def g703samples : Array (Bits × Bits) := #[(0x7e00fc07f00fffe01fe01ffffff80fc0fc07f803f03fffff003f803fffe007fff007e007fc01ff800fe01ffffff80003c00080860e0001e01f91c1e043c1ff07c0ffff8860e060fff07807fc03fc70e03c01c0ffff90402d99071cf80ece621f,0x48850042244430188411110c80001800804102040040a180610208911001200c00440620808842010405110c80200024800800008020124889080a8028092044010c300002000202048622421306040281100214c1040299102089000ca4212),(0x8000fff8000fe000001fe03ff007f000fff80003ffc1fc00ffc0003ffffffffffff80007fffe00000fffe03ff00001fc000f0707f0003e001fe1fe007c01e0003f0f80707f007f0e0f8007ffffff80ffc001ff0f8061864e1e249323350fec64,0x511186510419882a0292242112915028571240c51c91902148424912663644d11e90008dd12008ccaa928065024c816c108f050750942a081361561264112482250b08506b12290a4c80854ac6c680be80226a0e00e186460e24922325052c44),(0xfffffff0001fe01fffc00007ffff00000003fffe0000ffffffc03ffff801fffffff8000000000fffffc000001e00001007f80007ffffe07e00007ffe00f83ff0007f80007ff00ffff81ffc03ff000001fff000020873e038e3c439f39078,0x218a0c1400140a4414044412224c20040810a6108204a128482010840800461228220000205014504440050900600011002a800204441a002000008cc00280a60112a800452b08111281128113a00000594c005020801401041c418a29038),(0xffff00000000001fffe000000007fffffffffffc00000000ffffffffc0000001fffffffffffffffff00000000007e000001ff8000007c000007fffff800000ffc000007fffff80000fffffe00003fffffffe0000007c007c07c0fc07c1fc1f80,0x48580204080c1213108a09098a4449249a26246004008090a42a6824031226498a4514c6a2492864000081018826a122220ad0000006a1101859a53900001096a008224452b100000e66c780406244d532b00000087c007c0580bc02815c0b00),(0x1ffffffffffff800000000000000000000fffffffffffffffe0000000000000000000000000007ffffffe000000007ffffff800000000000ffffffff80000000000ffffffffffc000000000000007ff07ff800fff801ffe000,0x6ddcd3366f6edb9bdefb9dbdee774db6dab735f347acdafcff3f7dbfbf9b376dca75d6f6bb6dae7671d6f5b5ed3ffbb7fbaad0214947f7fdddd9b5bd22a59adff3bdfbc65ab918a92ffff7fff3fa66d5bab906634e7ff07ffd82fffa81ffeb12),(0x1fffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000007fffffffffffffff8000000000000000000fffffffffffffffffff00000000000000000000000007fff800000fffffe000000,0x6000c08181040c070c0e0e03878e38e0c3c1838630e0e0380c0e060c03c07003820700c07030078607060601c0cc3883d31bb26270000100000000000800e33cce3c7f7cde7ccdc40301018080080600c01884104b2d000000f76ffe000000),(0,0),(0xffffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000000007ffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000007fffffffff000000000000,0x7180e3070e0e1810181010300c0000000304060008010300c0307038301c07800c0418070381c078081818380e0711c33c0ce4458d87399e1e7df9de7331dc0400004000000000000844060203000018230020086034d2febfef000000000000),(0,0)]
def g703columns : IndexTree ColumnInfo := (.fork 6 (.fork 3 (.leaf [(12,16,163,0,4),(16,0,166,9,6),(0,16,175,0,8)]) (.leaf [(32,0,671,0,8),(2,0,701,0,8),(128,0,575,0,8)])) (.fork 3 (.leaf [(8,16,167,0,7),(0,24,163,4,5),(160,0,543,0,7)]) (.leaf [(1,0,702,0,7),(3,16,172,0,4),(8,0,695,0,8)])))
def g703autos : Array (List Nat) := #[[]]
def g703levels : Nat → Packing
  | 6 => g703l6
  | 7 => g703l7
  | 8 => g703l8
  | 9 => g703l9
  | 10 => g703l10
  | _ => emptyPacking
def g703index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 3 9 4 6 2 0 (keyg703l7)
  | 8 => lookupWord 29 103 7 11 7 0 (keyg703l8)
  | 9 => lookupWord 74 262 9 12 8 0 (keyg703l9)
  | 10 => lookupWord 10 37 6 9 5 0 (keyg703l10)
  | _ => fun _ => none
def g703 : Forest := ⟨703,10,fun j => g703samples[j]?.getD (0,0),g703columns,g703autos,g703levels,g703index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg703 : graphValid g703 (boundsBefore knownPrev_g703) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=2)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_6_0 : block g703 6 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg703_6 : block g703 6 0 3=true := sg703_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_7_0 : block g703 7 0 32=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_7_32 : block g703 7 32 26=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_7_58 : block g703 7 58 28=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg703_7 : block g703 7 0 86=true := (@block_merge g703 7 0 58 28 (@block_merge g703 7 0 32 26 sg703_7_0 sg703_7_32) sg703_7_58)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_8_0 : block g703 8 0 20=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_8_20 : block g703 8 20 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_8_52 : block g703 8 52 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_8_84 : block g703 8 84 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_8_116 : block g703 8 116 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_8_148 : block g703 8 148 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_8_180 : block g703 8 180 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_8_212 : block g703 8 212 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg703_8 : block g703 8 0 218=true := (@block_merge g703 8 0 212 6 (@block_merge g703 8 0 180 32 (@block_merge g703 8 0 148 32 (@block_merge g703 8 0 116 32 (@block_merge g703 8 0 84 32 (@block_merge g703 8 0 52 32 (@block_merge g703 8 0 20 32 sg703_8_0 sg703_8_20) sg703_8_52) sg703_8_84) sg703_8_116) sg703_8_148) sg703_8_180) sg703_8_212)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_9_0 : block g703 9 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_9_7 : block g703 9 7 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg703_9 : block g703 9 0 26=true := (@block_merge g703 9 0 7 19 sg703_9_0 sg703_9_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_10_0 : block g703 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg703_10 : block g703 10 0 1=true := sg703_10_0
theorem tablesg703 : checkedTables g703 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g703 0 0 0 = true)
  · exact (rfl : block g703 1 0 0 = true)
  · exact (rfl : block g703 2 0 0 = true)
  · exact (rfl : block g703 3 0 0 = true)
  · exact (rfl : block g703 4 0 0 = true)
  · exact (rfl : block g703 5 0 0 = true)
  · exact allg703_6
  · exact allg703_7
  · exact allg703_8
  · exact allg703_9
  · exact allg703_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low703 : Lower (vars 703) (graphGoal 703) 11 :=
  lower_forest (g:=g703) (i:=0) (hints:=536879361) (before_sound known887 valid887) geomg703 tablesg703 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps703 : List (Nat × List Nat) := [(703,[]),(863,[118,133,33,48]),(891,[118,130,81]),(957,[82,129,48])]
def known703 := extendKnown known887 11 maps703
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid703 : Known known703 := extendKnown_ok valid887 low703 (by decide +kernel)
abbrev knownPrev_g831 := known703
def keyg831l7 (i : Nat) : Nat := 0x20d00000470038a00346f1145c0b8900257a22017003
def keyg831l8 (i : Nat) : Nat := 0xf96e4d807a33bc4423d0001838c76809a1f001102d0a5a6470d9c39e26d190a2800189990618e2d7a000b0e98fcc16219000781e42a000d0a588c000000654f06384841a6a1985c00000000042e800074a110492a0536bbd13a00c03db3e4c50000000000b5b120479b21f723780147800062480000012350000001703a900003cecd99e1bba6e8484a362c81688dc4a5ec7b203d30649e39a05520e634634c4b710550fe13b2822a2c60eabf4ee121c1a000a03591e82110ab00c0c490d211027d52e086e2f41d4114e3622be8ad32fc05e4e5507cdbd358333a7311084224c6cc800049762a0003a0800124200060b880a828fdb3f1e603808000000000082505000901000007000001020200030701000405000c050e00020101030900001701021e0908021e000a3012000003
def keyg831l9 (i : Nat) : Nat := 0x180e413a4d1c3f5888a197ca7600c2fa326e60b408e643526085448648a873ebcbed34f8a7e04b0f501112f12318ecfa0e621b5b7949e81f808420790c2b049eef00858477306ca3e1e80e183cd832537d05d6a6e0acc0b8001e850000dbac2db0a280002180001d3a80012028000706283d415989b0390001d0dc4cc60702dc48f000000000002b30001e0d8001a16f82aa908001f1e00000000000506800080a0001a16000143fcaac000480750514172364825ab9a8af592d2cee37a8f7439d08d88b90c1e28b0b09bec01b40468d361f3480e09e816e21808ad8de0712335289131206dd2f003a0326048ea5409d834484a6ae40344b8787881472d822674ca6b2a6195ba106900c18a081cb8c5d08000098718e200022a8000603fe0214e800070aa5b7088002488e8205000172b8001ab0d0fa0005074e1354dc00070940005441a10920142e4ea8806000103c0000000100c0000001617feeda8c90ce78800001215a0a58bf8f982d9a9600000000000000110d273eae80019297896000000040b58bb2b78000b33f4fc00032aec3b12e502d3076ebf08a4f0726e1824106a1b5b8db4a73883fb280019385062ab8906fe2f3220010000541498d5301d43c22faa6a8a978dc109840311ac8efa9d20d72a9ee3c000000163a9a365b3589ec9880000003a2dd3ca08e88080b290f8900902b486832d06607008041208028200202000280400000000200000002a00000084a12008040208018000e00040000003058144a05000105e070100c1206030083614008000005028043a05040081210008400a090988006010000014110107c0e00
def keyg831l10 (i : Nat) : Nat := 0x4164df314b60800d8026000e9b764a20083b064755ac80006c0000008d7bd190484725326ebfc71bedb6a585b51540020014b107140008042005
def g831d6 (i : Nat) : Nat := 0x656d11bcca87942811be991213744275a52042c3224e74e408546449d694810a8c891bd790215191237af344261224ed46688482449dc04ab08bc8993d5849c0791333a4e9c00f2266d49d1801e44
def g831l6 : Packing := (11,4,3,0,0,6,0,g831d6)
def g831d7 (i : Nat) : Nat := 0x30d10000b0911a1202698201a1342030202031061b020006170203020000040620061000000000030200000000610228080000020800000030800000610034080000c2000610c2184308610061002729865c95e52906368ae1a8560a7fdfa7bdea765ce70dbe6e5ae68d9e64d8e625845fd6e5a55e5655453d4a515404ed364ad264851c45d12435023f4ec39ce2374d8334c830cbe2e4b42a4a427c9a2548a214801d4701ac6616c56144460ec300941a0540a01400bbe8858644bbc0854644dbc784c244bbe884c244bbd180c244fad6248244fad5248244fb93048244bbd6848244bbe8848244fb55144244bbd6844244bbd5844244bbc0858644bbe8844244fb53145e44fb51045e44dbd6745e44bbd6845e44bbd5845e44fb93041e44dbd1741e44bbd3841e44bbd2841e44bbd1841e44dbd2701e44bbd2801e44bbc089de44bbd3844244fba449de00bbe8811d309fe8811d30dbe8811d30dbd7891200bbe8854644bbc4858644bbc4854644bbc0850644bbd3810244bbd2810244dbc4791200dbd1791200dbd2791200dbe4441e44bbc4844244bbd1810244fb8404c244bbc484c244dbd3791200bbc4848244bf1180de00bd83851e00eb666912119f5180de00f9a448ce00eea6688a00faa4488a00ef26684600f7255846009dc3851e00fb24484600bb8484c200f3655912119ed2801d619bd4801d519dd3801d519ed2801d519ed289dd419bc484dc40f9843101309be8811d309bd489dd30fd233846009bc484dd109dd3801e449ed2801e449f51801e449bc784c244b9d3801e44bad2801e44bb51801e44bb4484c2119f5189dd20
def g831l7 : Packing := (83,3,3,0,0,10,0,g831d7)
def g831d8 (i : Nat) : Nat := 0x184681306240d831846118461184090800d0800005020485a16890c194616890c220cc1b448191a243065105a860c8d120646890321c4619014080004a0406a183405010000c08000002a28506500041080402808320181000000006100004080610000308081a04811042018ca018c81010a2214430008100820605a24308d121832b4481b0a01040100062014250800210061104020d0222840129044188006c284236142121420c1460a8c1228c1a182b055ceb2550a8d4f299528a3d46687d0aa0b3ee7b4f19d939e6ecd899d3125349c9071be2b43885d055fe3e3794f15ddbb6762eb1ceb98708de9b836b6ccd85abb5269ad21a1b3e640c6d8b30c5fabe16fada5a0b2d632c1578add592a8546a794ca8f514a013da764e299d3125849c9111d226424821019f43c076ceb1cc38e6f4dc1ae32a5dcac9542945009d92c24e4748990e1fe3e8780e61c235c640be1682944b0911181cc2d0460820c81180f001ff41e44ffa4f227fd10913fe90489ff4c244ff881227fe44803fea8c89ff58644feac708ff553847faa1c23fd10e11feac108ff550847faa0423fd4c211fe86108ff644847fa20423fd55211feac908fbe77912fe03c89ef41e44f7a2f227bd10913de90489ef0c244f7a61227bd51913deb0c89ef01e44ff467007fa44803fc8bc01fe49e00ff06f007f937803fc23c01fe51e00ff263007f941803fca8c01fe58600ff265007f942803fcb1401fe50200ff287007f611803f711401ef91200bfa2f005fd27802fe1bc017f4de00bf88f005fd47803fc88401fe48200ff061007f930803fc20401fe10e00bf88e987bc474c2fea3a61fe10130bfcee205fd17102fe938817f4dc40ff280207bd40103dea1081ef10c40bfceea05fe774c3dea0a817f9dd41bf80ea0dfc37506feaba837f59d41f7ac8a0dfe77546fe03aa37f0dd51bf88ea8dfe77586fe03ac3fe9de00bf86ea05fc47586fe8bc89ef10244f7a81227bd41912ff3ba217f0dd10bfa6e885fc47442fea3a217f55d10bface887f551442ff3ba417f0dd20bfa0f225fd470c2fe238617f45c30bfcee187ed62483f6a9241fe4c120bface905fd47483fc980617f11d20deccd08f7655847db224236f11d30f7489007da33803f511401fc84600
def g831l8 : Packing := (129,2,3,0,0,11,0,g831d8)
def g831d9 (i : Nat) : Nat := 0x5041a820d4c108a08645041a820d41088a025041bb69461b631410db1884d041ec62120af46fb2972a849a18ea581d8982a00ff587fd51ff507fd40ff103fd30ff0c3fd20ff443fe44ff803be44fd847fa00
def g831l9 : Packing := (14,1,3,0,0,9,0,g831d9)
def g831d10 (i : Nat) : Nat := 0x1441ff
def g831l10 : Packing := (1,0,3,0,0,0,0,g831d10)
def g831samples : Array (Bits × Bits) := #[(0x7f003f80fffff807f007ffffff01f80fc0fe01f80ffffff003f803fffe003fff007f003f807fc00ff803ffffffc0003c00001c18380003c000f98870707fff0781ffff8860e060fff0f00ff007f8e0e0700e03ffff9080464c1f1cf80ece621f,0x42220a400a10c0642042221900003000800410200840a180610409211100a00c00420301024200181009110c800200248000100020080248a0890050402922008110c300002000202090c1904260c040208802214c1080464812089000ca4212),(0x80003fff03f800000ff807fe00fe000fff0001fff01fc00ffc0003ffffffffffff80003fff80000ffffc03ff00000fc00071e01fc0007c003ffe0f807f83c0007e0f80707f007f0e0f000fffffff00ff800ffc0f804306187d649323350fec64,0x844508a40620a8144888422522a02856290628b211902148420924a62320d116900047a48044ca2a2500650125006c10870a01d4120341105320d82148244844a0b08506b12290a49010a258d8d00bd0112a80e00c306182544922325052c44),(0x3ffffc0007f80ffff80000fffff0000001ffffe0000ffffffc07ffffc01fffffffc00000000ffffffc000003f0000181ffe0000f80003f07f0007ffc00f87ff0007f80007ff00ffff0fff807ff00000ffff0001c18607278e3c439f39078,0x5080a3543284542a2854088924449c20082085344c8204a92a4d202485442046927491000082914d448a4005a482b02211815ea0024a82202a85d004694c28281560112a800452b082aa50ca50227a00002d53c0051c1860523841c418a29038),(0xffffc000000007fff000000000fffffffffffe000000000ffffffff80000001ffffffffffffffff000000000003c000001fe0000000fffffc007ffff800000ff8000007fffff80000fffff000007fffffff000000060007f8380fc07c1fc1f80,0x4160000000080c04281213048892249848830010008090240a080803011049824082614121404000010101801140200202400000001188380000111000000954008224452b100000c458c0080c484ca45800000086000150000bc02815c0b00),(0x7ffffffffffff000000000000000000000fffffffffffffffe0000000000000000000000000003ffffffe000000000ffffffff80000000000ffffffff80000000000ffffffffff8000000000000007fe07ffc00fff801ffe000,0x66f73a669b36e6f77ee7b7bdcee9b36d96ccf9a1eacdafcff3f6dbf7f999b6dc274eb7975b57267876df5b5ec9ff5b7fba241285248ddffbf3d945594c6b32dfe7bdfbc65ab918a92fffefffe7f4c6cb65c81a634e7fe07ffc12fffa81ffeb12),(0x7fffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000003ffffffffffffffff0000000000000000000fffffffffffffffffff00000000000000000000000007fff800000fffffe000000,0x180018204103038301c1c070f1c38e18f0c1c1830e0e0380c0e0c0c01e0700381038181c18078180e060600e1863883cb664c988e0100200000000000000e678ce3c7f7cde7ccdc80608030100080c06006084106a55000000f76ffe000000),(0,0),(0,0),(0xfffffffffffff800000000000000000000000000000000000000000000000000000000000000000000000000003fffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000007fffffffff000000000000,0x78e03c60c38604040c06060180000400200100060c10300c0307030701e03800c060c0206060380e07038380f0238c33c1499b16370e633c3ce7ee6e7e73bc0001004000000000000088008c06001010080183086015aaeaffff000000000000)]
def g831columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(6,0,825,0,7),(256,0,575,0,8),(264,16,39,0,4),(256,16,47,0,5)]) (.leaf [(2,0,829,0,8),(288,0,543,0,7),(2,16,301,0,5),(288,16,15,0,4)]))
def g831autos : Array (List Nat) := #[[],[130,81],[133,33,48],[82,129,48]]
def g831levels : Nat → Packing
  | 6 => g831l6
  | 7 => g831l7
  | 8 => g831l8
  | 9 => g831l9
  | 10 => g831l10
  | _ => emptyPacking
def g831index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 4 16 4 10 4 2 (keyg831l7)
  | 8 => lookupWord 46 158 8 13 7 2 (keyg831l8)
  | 9 => lookupWord 81 289 9 14 8 2 (keyg831l9)
  | 10 => lookupWord 14 38 6 10 4 2 (keyg831l10)
  | _ => fun _ => none
def g831 : Forest := ⟨831,10,fun j => g831samples[j]?.getD (0,0),g831columns,g831autos,g831levels,g831index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg831 : graphValid g831 (boundsBefore knownPrev_g831) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=1)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_6_0 : block g831 6 0 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg831_6 : block g831 6 0 11=true := sg831_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_7_0 : block g831 7 0 32=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_7_32 : block g831 7 32 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_7_33 : block g831 7 33 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_7_65 : block g831 7 65 18=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg831_7 : block g831 7 0 83=true := (@block_merge g831 7 0 65 18 (@block_merge g831 7 0 33 32 (@block_merge g831 7 0 32 1 sg831_7_0 sg831_7_32) sg831_7_33) sg831_7_65)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_8_0 : block g831 8 0 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_8_8 : block g831 8 8 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_8_40 : block g831 8 40 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_8_72 : block g831 8 72 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_8_104 : block g831 8 104 16=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_8_120 : block g831 8 120 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg831_8 : block g831 8 0 129=true := (@block_merge g831 8 0 120 9 (@block_merge g831 8 0 104 16 (@block_merge g831 8 0 72 32 (@block_merge g831 8 0 40 32 (@block_merge g831 8 0 8 32 sg831_8_0 sg831_8_8) sg831_8_40) sg831_8_72) sg831_8_104) sg831_8_120)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_9_0 : block g831 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_9_3 : block g831 9 3 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg831_9 : block g831 9 0 14=true := (@block_merge g831 9 0 3 11 sg831_9_0 sg831_9_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_10_0 : block g831 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg831_10 : block g831 10 0 1=true := sg831_10_0
theorem tablesg831 : checkedTables g831 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g831 0 0 0 = true)
  · exact (rfl : block g831 1 0 0 = true)
  · exact (rfl : block g831 2 0 0 = true)
  · exact (rfl : block g831 3 0 0 = true)
  · exact (rfl : block g831 4 0 0 = true)
  · exact (rfl : block g831 5 0 0 = true)
  · exact allg831_6
  · exact allg831_7
  · exact allg831_8
  · exact allg831_9
  · exact allg831_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low831 : Lower (vars 831) (graphGoal 831) 11 :=
  lower_forest (g:=g831) (i:=0) (hints:=12884910337) (before_sound known703 valid703) geomg831 tablesg831 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps831 : List (Nat × List Nat) := [(831,[])]
def known831 := extendKnown known703 11 maps831
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid831 : Known known831 := extendKnown_ok valid703 low831 (by decide +kernel)
def g767 : Forest := ⟨767,11,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low767 : Lower (vars 767) (graphGoal 767) 12 :=
  lower_discard (g:=g767) (ci:=(64,0,703,0,11)) (hints:=553656577) (before_sound known831 valid831) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps767 : List (Nat × List Nat) := [(767,[]),(991,[118,133,33,48]),(1019,[118,130,81]),(1021,[82,129,48])]
def known767 := extendKnown known831 12 maps767
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid767 : Known known767 := extendKnown_ok valid831 low767 (by decide +kernel)
def g1015 : Forest := ⟨1015,11,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1015 : Lower (vars 1015) (graphGoal 1015) 12 :=
  lower_discard (g:=g1015) (ci:=(0,16,487,0,11)) (hints:=22028484865) (before_sound known767 valid767) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps1015 : List (Nat × List Nat) := [(1015,[]),(1022,[118,133,33,48])]
def known1015 := extendKnown known767 12 maps1015
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1015 : Known known1015 := extendKnown_ok valid767 low1015 (by decide +kernel)
abbrev knownPrev_g895 := known1015
def keyg895l9 (i : Nat) : Nat := 0xdaed2613d617b13000000311000723032e46e2b73a90e0005c0a2010304c61d13cc3f630c2e04d0002a7e87344804539c0100014e28814a2c534953850910fd2f535328a4010a0059ca73b925000a33d37000fad642c1582aeb3916621c84000bc12ab745000f4b000d3630c88cc8e000c180001c4d27e8211b00000022d61e00000000003e686d22500810041000292ec8c2cd316297bf31c8cb000548000690f0de0b5ac31a507dbcc91202147724e19706334b14c08c12a1fb4310187201c4820100000001604607220820b081428000280000a304040024100
def keyg895l10 (i : Nat) : Nat := 0x96baa7526f5ea11379f3099437c1f781910f0e0048fa439f7e7b57d23340000c5321802dc2e000b6fceedc29ec3d06183566deb1d4fd93da843f48478001c1d87da530000ca630765bf97841200053a9e2d9463a601c4dbae2689c18c0000f01ef1e8839a587824ad64f95c068ef97645a34000000000508d33e384cbd79b005f89b0000000000000000511cd2b175000236a8b00006ccdbdc00000000000033340009b08000000000868a8400000000001bc29a91e900010b00003f30004cbf23b6de771800000000082b0000000e3b00076561ca5f294baada148a252df90a5b158c6520e0b6dbade560402b4c72af206e0003c1588689ad25011c000cde1a26c225c4000000370c6dba82e0653c400005fc8fe4742c713c0002dde0000000000001683ba20000834f979756ae556a4723f6d96d438881b598da6444000c52c994a00e440000a08001ae6e613f0bd9daec479fce6b7dc0114d29f852ccbd3dd42a403ee5061ac076fa3c12c4c5acaaec82801741561db6ab4773010bf04180002df22e10d819dafc75c34e45e19a7bed92aef5c7aef8c8ad900072bc000150000597fda6729a7a5b887f28032344923ef6ad531802331ce661426c1035786493620000000f94d19d3d80b9ed0000011776d312e302884fd8d343157f740000000004ec28e2e02c1e8000cf47cd213e9b80007e84a30e61d249d685d78833ea0a8774c06df390990f191dbd54e730818878001867f49973bf73e075386daec85eb47500e218e979dbb23816427af5c65199ba51eac3da80010db06ae123b584b4c5238bf22b91085167c6ac16700003188002608714c1b7305f2d6791001165542000742432c000000000622f94f0e81660000056446237d202fc30858f779af0c444b4b8a5e19d647782ea8cb19e5afb0a8405da5d1155152f842c87f52a503e09d0632e85b002141101018000a008081a0300018240b0a034140300840260c0000418190080808000000c0802020140a000000004010e8000a01058a00401010041605038001008010481a0403004082602814020302808340001008021b03000000200044800600004460100000261100804062a0085804000380000050006c160104004281e118183405020240e02
def keyg895l11 (i : Nat) : Nat := 0xa15000061033f48bd664dc034e2000412000f11000000955316589f028b052415be2740e9605ce000b5801393c400d3fe34000d190006358cdc6300000095002b000e37000da4310000122ca9000c6435fb4100025cab5000c90a56b8e7cb745e3e00005a3201179b8000453000f99438f2800030da47000c0f000000a5dcaa000b66ea011eae45983440000a6000854000000000d3a0004d1168a40cd44a712346505e72d94c5c3a433d7a59000bab84ff911db38f000000f9c91b3c4000000739000fbc000508000000000ca1846a1fb255a8000000f36e4b00000000022a7622e574900000000b000000b06932000000fd3000a0453b000b2c4420677d26217317a3b0172f63d2d8c0550c3b744e23082ebd525751481dbc06bd51ab1c107051d5280a1186b6000729bc579712600000044a7091bb000000000d0100000208000100000a00010000010b0318011a0003001400060c000e0202000802010c02020202012c010000020100001f07
def keyg895l12 (i : Nat) : Nat := 0x6a6c001628c123f3c628802960000000000000000154900002c200002c9ce05618026a006980001e4000000180000002000000001040
def g895d8 (i : Nat) : Nat := 0x1c61f0041400800000000000140080000000000000000000000000000003c01f007c0100043e00f802010f803e00f803e0080820108103e008043e00f8020f007c01f007c01f007c01f007c01f007c01f007c01f007c01f007c01f007c01f006eeb82dbb36c8b0ebeae6b4abeaaa96a0a6e8da22839fa799d26f9aa659825b95a519324790a3d8e2338ba298921f86a15842027d1e6785d3715b76a59b6357f5c563555474e52b4750f428fc3b8e0348c42d8a82688c1f87018854118380a81c03800cef5c699121308df568899de009ee12939442009eeaa8494c2009ee129794c200b3d5a8899de11b3d5a8099de11b3d5a8309de11b6d129309de119bd5a8899de11b6e129309de009bdaa9690e2119f9aa9291e2119bdaa9690c2119edaa8494c2119ed129794c2119f9aa9291c2119dd56a995c2119fcaa9091ce119ed1293902211bbc5a83984600bf84a87984600bdc5683884600bf84a87384600bdc5687384600bbc5a87384600b5e568899de00b5e568199de00b5e568389de00a5f568899de009de568899de009deaa9590e2009deaa9590c6009fa4aa994c6009be5aa995c6009fcaa9191ce00bec1293084600be6129308ce00f749de3384600b5e568319de00a5f568395e010a3f5a8395e0108fb4aa994e1108efaa8494e1108ef129794e1108df56a995e1108bf5aa995e1108ef129894c1108bf5a8899de11a9f568195a030a3f5e8195a0308bf269715a030ccf1215906130acf56819121308ef6687112130f745c5315c1308ef129891c530adb568314a070abb4a8195a0309ed12939442118fb668734a010afa428734a010af9468734a010adb568734a010abb5a8734a010af6428794e010af5468794e010af34a8794e010a7b4a8395e010ab75a8794e010af34a8734e010ab75a8734e010add4687356010adb4a87356010a9f5a873560108bf668735a010abd468735a010a7d468395e010ad7568794e010
def g895l8 : Packing := (79,4,5,0,0,10,0,g895d8)
def g895d9 (i : Nat) : Nat := (if i<1 then 0xa8487108dfd5e408846fea7204423df5739de11efab84ef08dfd5e530847bf0713bc01df8189de00efc1ccef0077e06677803bf1133bc01fd9738ce00fec98c67005fe22633803bf4ef19c01fd9718ce00fec38c67007f61e633803fb03319c013fc898ce00ff8b8c23007fc4c611802ff11308c01dfa7784600fed19c23007fc5ce11803fe0e708c01ff07884600ff81c423007fc1e611803fe07308c01ff08984600ff93bc23007fc8ce11803fb11319c01ff110846009fe44c23007fc5c211803fe26108c01bf48984600efb3bc23005fe22573802ff532b9c017f9191ce00bfc44ae3005fea6571802ff27238c01ff1714c600bfcbca630077e0c677802ff53298c017f9790c600efcb88f1005fe4e478802ff2323c401fd9310e200bfcbc871005fe46438802ff2f20c4017f93906200efcb9cef0077e5c677802ff1133bc01df9319de00bfc44a63005fe424714c27fb1238a61df9715c130fec98ae0987f60e5704c2ff532b8261fb97012130bdf4c890986ef5c4484c3778e224261bbd7012130dde8c890986ef064484c377d3224261bf57146030bde24a30987f54c4184c3778900c261bf51806130bbeac830986ef122884c37f2e1442613fd19a21309fec48e2185fda65738475f8e2b4061afd195a030d7e0cad0186bfa65680c3778908c261bf90802171bf694810b8dbf5a6885c75fad3442e33fd09a21719ff4ca1038f7e025715c2bfd32b8ae1df5714c5709fe44a62b85ef125385c37ba701c2e16fd690e170efab8830b84ff225714c2efab3442e19fd71a2170dbeacd10b84ff4e6885c27fa33442e13fd890c470dee98a70384ffa65381c37da62940e1bec314a070df69ca50386fb465281c37ea628c0e13fd39460709ff4ca30386fd460185c33f872bc0219fe995e010d7eb9ad0086bf1cd680436fae6ac021b7c7356010deeb9a70086f71cd380427faf29c0213fe994e010deebca70086f71e5380437bd329c0219fd395e010df639a50084ff22573846dfad239c2377d591ce11bf6948e708dfd46473846ff21239c237f5794c611efab8ae108cff22570846fda52384237f5191c211fea98a6108efb5cd280435fae2b40613fe99460309fe44ae6884ff62570442f7892982213fd894c1109ff4caf08867f5e078442f78929c2213fd794e110dde24a70884ffa65384437ba701c2213fd39a21109fec48e60867f5cd780433f8e6bc0213fd79a21109ff4caf0084ff5e5180c25fad3442e3779590c600bdc24a610047fa65780425fd32b4061df27784600fe919c23005bd5a473846eeab239c237e5291ce11bbcac871005bd5a43884677d32242617e5291c2119beacd10b85fc46473802778929c2213de994e010bda24a6108df94a478846df2d239c016f5690c211bbcac8e7004fba65281c2fd25239c017f1091ce11 else (if i<2 then 0x400000000000541232510000000000008c24a1031840ca1003f00b803c01e0080092082100402c8c9a033184382cc08265041240088100680611c026004102200840e00b0041c01e0083803c0123e017006941040e3e0101f00b803c01e00801c01e00f302081cdc02070041b8040e00f007803c0108e01700447805c01e00f004238040bc02e0083803c01e00f007803c0108e017007803c01e00f007803c01e00f007803c01e00f007802464a2280f0078020280f007803c01e008183700c1020bc02e0080102060c0bc04e504170041c01080ae0184700b803c01e0081f00b9b83958c9c7c053ca4f806e3e6e540271f372c3c4701b9a27962380bc7cdc1cb8140c07e3e6e0e5c0a0603f37014f296978f80a794b0a55c7cdc0565e329e5e027314f2f0103f8f9b27943b2281055c7cdc051806e3e0e56621571f37014f2e01f8f9b94049c7cdcb0f11c06e3e6e54021571f370139b80a794b4bcdc053ca51806e3e029e52c2c571f3447014ab8f9b80aca55c7cdc053cb807ef7ef2eedee8ee3ed6ec9ebceafea2e95e88e83e76e69e64e57e4ae3de38e23e16e09dfcdf7df2dedde8ddbdcedc1dbcda7d9ad8dd80d7bd76d71d6cd67d5ad55d50d4bd3ed39d34d2fd2ad25d20d1bd0ed09d04cf7ceace5ce0cdbcd6cd1ccccbfcb2cadca0c93c8ec81c74c67c5ac55c50c4bc46c29c1cc17c12c0dc08c03bfebf1becbdfbd2bcdbc8bc3bbebb9bb4bafbaaba5b98b83b7eb79b74b6fb6ab65b60b5bb56b49b3cb37b2ab25b18b13afeaf1ae4ad7ad2acdab8a83a76a69a54a3fa2aa0d9f89e39de9c99c49b79aa9a599898b98697996c95794a93593091b9068f98ec8df8da8d58c88bb8a68a188c88787a86586085384683982c81780a7f57e87db7ce7b97a479779278577876b75e75174472f7227157086fb6ee6e16d46c76ba6ad6a069368667966465764a63d63862b61e6116045f75da5cd5b85ab5a659957455f55254d54052350e5014f44e74d24ad47845341e3f13b437734a31d2f02cb2a626122c2071ca1a517014b1260f90c409706a03d000efa984ef08f7d0c277847be8733bc23df4099de11efa44cef08cff22573802dfad239c0177d591ce00bf6948e7005fd46473802ff21239c013fc895c600bfc848e3005ef12530846efab218c017f9090c600efcb8ae1007f64c530802ff2f298401fb8494c200bfcbca21005fe4e510803bf2e13bc013fc899de00efc984ef0077e442778033f9133bc01fd9308ce009fe44a63004ff22530846dfad2184237f5190c211bfabca2108dfd4e510847beae33bc233fc899de11bfa44ae708dfd42473846fe912b84237f6995c211bfa9c8e108ffc5c130846fe9133bc23fb4494c211bfa44a6108dfda6530846feaf218423df5701e211bfa9c8f108dfd42478847faa601c4237f5790e211bf else 0x7007803c01e00f007803c0100707802008084049820232611285983c0100000e00f00780202326112858c3c0100000015040001004000000001304006609304000000065090040c6160081803c01630b2840000181209c6c01000000018020e00b30))
def g895l9 : Packing := (252,3,5,0,0,12,0,g895d9)
def g895d10 (i : Nat) : Nat := (if i<1 then 0x13308c03cc20560263469b0123074623015288c0311805192e01e30f8068f0083e0126122b0112e0108c02102700f187158091d4aa501f1e6c19602a42a529c463cd832c052852a83e3cd832c04c852a9388c79b06580a0f8f360caa0c1f1e6c195498463cd832a7307c79b0655460f8f360539541d4a714231e6c1960255290e231e6c196024463cd832a9308c79b065546118f360539539e4c755231e6c1950253a954231e6c19602442ac79b0654e74ea9488c79b065809118f360539551e5494f231e6c1950254aa4e231e6c19602552712231e6c1960263871328508c79b2e0509158f360ca1ce1c463cd8329a408121e50ac79b2e0507158f360ca20e24563cd83288389158f360ca69125063cd9421c548101e489c79b2e050ac79b009ca20e271e6c194a2b1e6c194a284c8111c3e3cd970284e3cd8328710790a93a9118f360cb0142b1e6c1943883a854a43e3cd832c0487c79b029caa8ea55280f8f360cb012a540a0f8f360cb012a94090f8f360cb0121d563cd832a838754a5463cd832c04a7918f365c080ea6463cd970203aa918f365c080e2b1e6c020899063cd272c8363cd804122e6c0272882e3cd83287106c783287265cd83288285c79b0650e20caa3e3cd970203c65e2ed16a8a4c4a220f0ed869c2ca14d093843c1b609903280fc015fc8fca7d4be59ef8f627a7bcb9e28efa7703afdd58e9273c395dc7ae1c6fdb74db72da66c635c9abed4c695b461a0aceb66531fd868bf05d2add968eb18574aacd4dea2b4fe273532e953487a36512a85f40d9f5cf267483891b8cd3066231617f4b8e57c2a314789ec4ab23a90a87e83b01bd0cd85e42ae13c08d03fc1c80c9058c26810c07202d411a06501b0003ff1c430ffe11803ff5cd10ffd71443ff4c510ffd70443ff4c110ffd78443ff8ce00ffc78443ff4e110ffc38443ffa2110ffe77803ff5c430ffc73043ff0c600ffd31803ff1c600ffd71803ff5ce11ffc73847ff1ce00ffd73803ff5c211ffc70847ff4c211ffc30847ff9de11ffd73043ff4e170ffc385c3ff46170ffc185c3ffa2170ffd085c7ff5c570ffd311c3ff0c470ffd315c3ff02171ffd714c3ff1c530ffd704c3ff46130ffc184c3ffa2130ffe885c7fd9de11ffa33803fd4c211ffa77803fd02211ff438847fe06200ff478847fd0c211ff970803fe44200ff838803fe1e200ff8318037f9de00ff931803fe1c600ff971803fe1ce00ff611803fe5ce00ff930802ffa2171bfd081c77f5c570bfe885c2ff4e070bfd181c3fe5c130fbc484c2ffa2130bfd180c2ff5e110bfd38442ffa2110bfd78043fe84600bfd38043fd5c211ff473847fd5ce11ff571847fd4c611ff470847fd44211ff211803f68ce00dfa77802fb4a070bbc484c2fb4a010afd680c2f74e010b7d58042bf5a0109fd780437d9de11 else 0x2300a4271180980229188c04129446020a4c1f010487c03469b00e429118098029700b004407c0390a84602231180623008407c0312944602080f80629188c040f8041c56018815806230085260f8081c4601890f8061c4601c7541f0104601664d807985601e6469b0)
def g895l10 : Packing := (105,2,5,0,0,13,0,g895d10)
def g895d11 (i : Nat) : Nat := 0x2482a39a09474151cd04a39891ca8e682521054734129062878e68099484473404ca418a2639a09472111cd04a39062891c88e68254144903c73412a078e696000c44734b00067fdd66857850d1a394bc21c520a400ffae3ff1c7feb87fc70ffa61ff0c3fe887fc10ffc23ff803fb08ffa00
def g895l11 : Packing := (12,1,5,0,0,10,0,g895d11)
def g895d12 (i : Nat) : Nat := 0x3300a4ff
def g895l12 : Packing := (1,0,5,0,0,0,0,g895d12)
def g895samples : Array (Bits × Bits) := #[(0xfffff0000800001f800207810f0000007800001c0c1c0000f8000f98870707fff00ff007001fc0f800007c007043c060ff80fe03f01fffff8830700c0fffc3f003ff003fe381c0f003807fffff058c01080464c1f0d984e4a2331cf80ece621f,0x6430000000091016908205000a0008004900001000100200a90a089005040292200190010004002182086420604148402a00640110144343000010000100839032390219830080a02200510a98058c010804648120910064a222089000ca4212),(0xf8000000700001e000043801f000001f800071e00fe0001f0003ffe0f807f83c0ff0007803e0ff0007ffffff807c007f03ff00000fe03e00703f800ff0703c0003fffffffc01ff0003ff807c00001024306187d643260b07f84c9323350fec64,0x80809000500000a0200410019020400d820870a00ea0880d02105320d821482440b000180020450000a08a0d000c000100c6004084a02c08503582449051240041424c6634017a0044a500700100102430618254420402021008922325052c44),(0xf8001fe0000183ffe00000fe0000181fff00003e00003f07f0007ffc000000f8003ff0007f81f8000ff80007ffc0001fc0fffc0007fc0000fff803ffffc1fffc01ffe000003ffff800051e0c1c18607278c384c78c470e3c439f39078,0x2d15220d8101761241182fda00440b604411815ed00112a08402a85d004694c28404858042d71042a81b2040ba80027acc082894095d80112d40008b2d820aaa941cb28089f400000b5a7e000a51e0c1c186052388384c50c47041c418a29038),(0x30003e0000001fc0000001f0000001fe00000003fffffc007ffff8000000000ffffc000007ffe00000ffffff80000001fff00000007ffffff000003fffffe000001ffffffffc000000008600060007f8380fc0707f0780fc07c1fc1f80,0xc0204420001a0004020280000000d00400202400000000463078000011100000088908552800000516c04084446a69000000414ba400202242295a200000314563800403120994c560000000108600060001500007c0202f0300bc02815c0b00),(0xfc0003fffffffe000000001fffffffe0000000003ffffffff80000000000ffff00000000007ffffffff00000000000001ffffffffff8000000000003fffffffffffe00000000000000000e7ff07fe07ffc00fff807ff800fff801ffe000,0xf63a7ee4023fbb7ff7a285488a89fdb6ff7a241242922377ff7f3d945594c6b32dddfc55aa1424a7dffdffee666b6d486a1275effe7ef7fbc32d5b218544bffffbffff3fd30d96e57203531a9ce7ff07fe07ffc12fffa07ffb22fffa81ffeb12),(0xfffffc00000000000000001fffffffffffffffffc0000000000000000000ffffffffffffff80000000000000000000001ffffffffffffffffffffffc00000000000000000000000000000f80007fff800000fffff800000fffffe000000,0x438776bb502000040000100010e1c7107cb664e4c4780400200000000000000eee2efecf79f6ce0490010808003010802481f2cf8b38bc7fbe6fcfce6f20018100180400101801800c042020f80006a55000000f6eff800000f76ffe000000),(0xffffffffffffffffffffffe0000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000fffff8000000000fffffffffff000000000000,0x7c07b72b9c3c4707cac99c231c8100004000008000400020400000000000000f0fcf67f39eb8f7e71e71f0ff73be7cf338f983080c00c004000c0208080186020820080020008600101800c0ff4a90000000000dfbfdfdeff7000000000000),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffff00000000000000000000000,0x78008084421c19878153661cce10e186781499b0b1b8398c783ce7ee6e7e73bc0000000000000000000020000000000004000000010010000000000000002080010c03000402008006060430000b5695aaeaffff00000000000000000000000)]
def g895columns : IndexTree ColumnInfo := (.fork 10 (.fork 5 (.fork 2 (.leaf [(0,16,367,0,11),(16,0,358,9,7)]) (.leaf [(25,0,358,0,5),(64,0,831,0,11),(0,17,332,34,6)])) (.fork 2 (.leaf [(4,0,891,0,11),(32,0,863,0,11)]) (.leaf [(2,0,893,0,9),(1,0,894,0,9),(8,0,887,0,9)]))) (.fork 5 (.fork 2 (.leaf [(256,0,639,0,9),(12,0,883,0,8)]) (.leaf [(288,0,607,0,8),(320,0,575,0,8),(2,17,332,32,5)])) (.fork 3 (.leaf [(256,24,99,4,5),(0,24,99,260,6),(5,0,890,0,7)]) (.leaf [(6,0,889,0,8),(33,0,862,0,8),(66,0,829,0,8)]))))
def g895autos : Array (List Nat) := #[[],[82,129,48]]
def g895levels : Nat → Packing
  | 8 => g895l8
  | 9 => g895l9
  | 10 => g895l10
  | 11 => g895l11
  | 12 => g895l12
  | _ => emptyPacking
def g895index : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 36 125 7 12 7 1 (keyg895l9)
  | 10 => lookupWord 121 419 9 13 8 1 (keyg895l10)
  | 11 => lookupWord 53 213 8 12 7 1 (keyg895l11)
  | 12 => lookupWord 9 46 6 9 4 1 (keyg895l12)
  | _ => fun _ => none
def g895 : Forest := ⟨895,12,fun j => g895samples[j]?.getD (0,0),g895columns,g895autos,g895levels,g895index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg895 : graphValid g895 (boundsBefore knownPrev_g895) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=3)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_8_0 : block g895 8 0 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_8_32 : block g895 8 32 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_8_64 : block g895 8 64 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_8_78 : block g895 8 78 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg895_8 : block g895 8 0 79=true := (@block_merge g895 8 0 78 1 (@block_merge g895 8 0 64 14 (@block_merge g895 8 0 32 32 sg895_8_0 sg895_8_32) sg895_8_64) sg895_8_78)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_9_0 : block g895 9 0 26=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_9_26 : block g895 9 26 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_9_58 : block g895 9 58 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_9_90 : block g895 9 90 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_9_122 : block g895 9 122 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_9_154 : block g895 9 154 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_9_186 : block g895 9 186 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_9_218 : block g895 9 218 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_9_250 : block g895 9 250 2=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg895_9 : block g895 9 0 252=true := (@block_merge g895 9 0 250 2 (@block_merge g895 9 0 218 32 (@block_merge g895 9 0 186 32 (@block_merge g895 9 0 154 32 (@block_merge g895 9 0 122 32 (@block_merge g895 9 0 90 32 (@block_merge g895 9 0 58 32 (@block_merge g895 9 0 26 32 sg895_9_0 sg895_9_26) sg895_9_58) sg895_9_90) sg895_9_122) sg895_9_154) sg895_9_186) sg895_9_218) sg895_9_250)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_10_0 : block g895 10 0 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_10_12 : block g895 10 12 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_10_44 : block g895 10 44 13=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_10_57 : block g895 10 57 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_10_89 : block g895 10 89 16=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg895_10 : block g895 10 0 105=true := (@block_merge g895 10 0 89 16 (@block_merge g895 10 0 57 32 (@block_merge g895 10 0 44 13 (@block_merge g895 10 0 12 32 sg895_10_0 sg895_10_12) sg895_10_44) sg895_10_57) sg895_10_89)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_11_0 : block g895 11 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_11_2 : block g895 11 2 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg895_11 : block g895 11 0 12=true := (@block_merge g895 11 0 2 10 sg895_11_0 sg895_11_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_12_0 : block g895 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg895_12 : block g895 12 0 1=true := sg895_12_0
theorem tablesg895 : checkedTables g895 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g895 0 0 0 = true)
  · exact (rfl : block g895 1 0 0 = true)
  · exact (rfl : block g895 2 0 0 = true)
  · exact (rfl : block g895 3 0 0 = true)
  · exact (rfl : block g895 4 0 0 = true)
  · exact (rfl : block g895 5 0 0 = true)
  · exact (rfl : block g895 6 0 0 = true)
  · exact (rfl : block g895 7 0 0 = true)
  · exact allg895_8
  · exact allg895_9
  · exact allg895_10
  · exact allg895_11
  · exact allg895_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low895 : Lower (vars 895) (graphGoal 895) 13 :=
  lower_forest (g:=g895) (i:=0) (hints:=12901687553) (before_sound known1015 valid1015) geomg895 tablesg895 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps895 : List (Nat × List Nat) := [(895,[]),(959,[118,130,81])]
def known895 := extendKnown known1015 13 maps895
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid895 : Known known895 := extendKnown_ok valid1015 low895 (by decide +kernel)

theorem two_count {α : Type} (p : α → Bool) : ∀ (l : List α) (i j : Fin l.length), i ≠ j →
    p (l.get i) = true → p (l.get j) = true → 2 ≤ l.countP p := by
  intro l
  induction l with
  | nil => intro i; exact i.elim0
  | cons a l ih =>
    intro i j hne hi hj
    have pos : ∀ k : Fin l.length, p (l.get k) = true → 1 ≤ l.countP p := fun k hk =>
      List.countP_pos_iff.2 ⟨l.get k, List.get_mem l k, hk⟩
    rw [List.countP_cons]
    refine Fin.cases (motive := fun i => i ≠ j → p ((a :: l).get i) = true → _) ?_ ?_ i hne hi
    · intro hne hi
      refine Fin.cases (motive := fun j => (0 : Fin (l.length + 1)) ≠ j → p ((a :: l).get j) = true → _) ?_ ?_ j hne hj
      · intro h; exact absurd rfl h
      · intro k _ hk
        have := pos k hk
        have ha : p a = true := hi
        simp only [ha, ite_true]; omega
    · intro m hne hm
      refine Fin.cases (motive := fun j => m.succ ≠ j → p ((a :: l).get j) = true → _) ?_ ?_ j hne hj
      · intro _ ha
        have := pos m hm
        have ha : p a = true := ha
        simp only [ha, ite_true]; omega
      · intro k hne hk
        have := ih m k (fun e => hne (congrArg Fin.succ e)) hm hk
        omega


def primary3853 (i : Nat) := inputs.getD i zero
def plus3853 := primary3853 0
def minus3853 := neg plus3853
def bank3853 (b : Fin 9) : List Sig :=
  List.ofFn (fun i : Fin 9 => if i=4 then zero else primary3853 i.val) ++
    [minus3853, if b=4 then zero else primary3853 b.val]
def row3853 (r : Row) (i : Fin 9) := if i=4 then false else sample r i
def flip3853 : Move := (~~~(primary3853 4), primary3853 4, Fin.ofNat 512 16)
def perm3853 : List Move := flip3853 :: [83,114,99,33,16,64].map swapRows
def all3853 := vars 495 ++ [minus3853]
def minusBank3853 := vars 494 ++ [minus3853]

theorem lower3853 (m L : Nat) (hv : boundsBefore known895 m = L) :
    Lower (vars m) (graphGoal m) L := by
  rw [← hv]; exact before_sound known895 valid895 _
theorem plain3853 : Slice (vars 495) (graphGoal 495) one 13 :=
  slice_correct (ms:=[]) (base:=vars 495) (G:=graphGoal 495) (by decide +kernel)
    (by rfl) (by unfold proper; decide +kernel) (lower3853 495 13 (by decide +kernel))
theorem flipped3853 : Slice minusBank3853 (graphGoal 495) one 13 :=
  slice_correct (ms:=perm3853) (base:=vars 895) (G:=graphGoal 895) (by decide +kernel)
    (by decide +kernel) (by unfold proper; decide +kernel) (lower3853 895 13 (by decide +kernel))
theorem doubled3853 : Slice all3853 (graphGoal 495) (subcube 1 0) 11 :=
  slice_correct (ms:=fixRows 1 0) (base:=vars 494) (G:=graphGoal 494) (by decide +kernel)
    (by decide +kernel) (by unfold proper; decide +kernel) (lower3853 494 11 (by decide +kernel))

theorem useSlice3853 {T bank d L k t S} (run : Live T k t S)
    (sl : Slice bank T d L)
    (av : ∀ w ∈ S, availableB d bank w = true)
    (lt : k < L + S.toList.countP (isMaskedConstant d)) : False := by
  have cut : poolCut d L k 0 bank S.toList = true := by
    simp only [poolCut,Nat.add_zero,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
    exact ⟨lt,fun w hw => av w (by simpa using hw)⟩
  have h := poolCut_sound sl [] (by rfl) S.nodup_toList cut k t (Nat.le_refl k)
  exact h (by simpa using run)

theorem eliminate3853 (b : Fin 9) {k t S} (run : Live (graphGoal 495) k t S)
    (hk : k ≤ 12) (sub : ∀ w ∈ S, w ∈ bank3853 b) : False := by
  have pkg : ∀ b : Fin 9, (bank3853 b).all (fun w =>
      (availableB (subcube 1 0) all3853 w) &&
      (decide (w = minus3853) || availableB one (vars 495) w) &&
      (decide (w = plus3853) || availableB one minusBank3853 w)) = true := by decide +kernel
  have prop (w) (hw : w ∈ S) := List.all_eq_true.mp (pkg b) w (sub w hw)
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at prop
  by_cases hn : minus3853 ∈ S
  · by_cases hp : plus3853 ∈ S
    · apply useSlice3853 run doubled3853 (fun w hw => (prop w hw).1.1)
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp (by simpa using hp : plus3853 ∈ S.toList)
      obtain ⟨j,hj⟩ := List.mem_iff_get.mp (by simpa using hn : minus3853 ∈ S.toList)
      have neq : plus3853 ≠ minus3853 := by decide +kernel
      have ne : i ≠ j := by intro e; apply neq; exact hi.symm.trans ((congrArg S.toList.get e).trans hj)
      have ci : isMaskedConstant (subcube 1 0) (S.toList.get i) = true := by rw [hi]; decide +kernel
      have cj : isMaskedConstant (subcube 1 0) (S.toList.get j) = true := by rw [hj]; decide +kernel
      have count := two_count _ _ i j ne ci cj
      omega
    · exact useSlice3853 run flipped3853
        (fun w hw => (prop w hw).2.resolve_left (fun e => hp (e ▸ hw))) (by omega)
  · exact useSlice3853 run plain3853
      (fun w hw => (prop w hw).1.2.resolve_left (fun e => hn (e ▸ hw))) (by omega)

set_option maxHeartbeats 0 in
theorem result (b : Fin 9) (D : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo D)
    (hs : D.size ≤ 12) : ∃ x : Fin 9 → Bool, x 4 = false ∧
      D.eval (List.ofFn x ++ [!x 0,x b]) ≠ edge x := by
  by_contra! hc
  have hr : ∀ r : Row, row3853 r 4 = false := fun _ => by simp [row3853]
  have data : ∀ b : Fin 9, ∀ r : Row, (bank3853 b).map (bit r) =
      List.ofFn (row3853 r) ++ [!(row3853 r 0),row3853 r b] := by decide +kernel
  have values : ∀ r : Row, bit r (graphGoal 495) = edge (row3853 r) := by decide +kernel
  have eq : (execute D.gates (bank3853 b)).getD D.output zero = graphGoal 495 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute D.gates (bank3853 b)).getD D.output zero) = bit r (graphGoal 495)
    rw [←b_read,execute_bits _ _ _ (fun g hg => (hf g hg).1),data,values]
    exact hc (row3853 r) (hr r)
  have hout := get_rep (execute D.gates (bank3853 b)) D.output
  rw [eq] at hout
  have hp : proper (graphGoal 495) := by unfold proper; decide +kernel
  have cin := hout.resolve_right (fun h => h hp)
  obtain ⟨k,t,S,hk,run,sub⟩ := extract D.gates _ hf hp cin
  exact eliminate3853 b run (hk.trans hs) sub

def p3853r6 (i : Nat) : Nat := 0x1b08dc76109358d6250a00
def l3853r6 : Packing := (1,7,6,0,0,0,0,p3853r6)
def p3853r7 (i : Nat) : Nat := 0x6140400b47080080414020a0107c1c3c0e1e07088107e1c2f0e1ede8e3ded9d4cfbeb9b4a39e99887766554433221100a27dc52e1a624d7280289f718a9615535ca008badc42e9835c96280289f714b86989350a00d19db76109358d42802ce330d976116250a00d1adb76109358942802d3371c9358d6250a00f28d8424d63589428032f85c9b02856260600cb8d846c8a35d1318027a5718b35d1414c6009f85c22cd74505318035386d9722457148200d561b55c8915c5208035706cd722457148200d519b75509354d42802d3271c9358d6250a00b6c1c124d63589428027e070cb158942506009e91c62cd74505318027e0708b35d1414c600
def l3853r7 : Packing := (22,6,6,0,0,8,0,p3853r7)
def p3853i7 (i : Nat) : Nat := 0x4
def p3853r8 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x2bcc5cae919a83004fd1b328562506009f3166d3a84a0c0136e6dca35094180275cdb146a1283005fa0b15894250600a7d170cac44a0c011ee6d0a8a65318023f4d91514ca630047e9b2aa9974c6008f7576d212e98c0157a6ca999dd31802b74d9533332630047e9b2aa9954c600aed3654ccaa98c011fa6caaa6513180276cdb146ba263004fc9b228d744c60087f170d4aa898c015ea6ca9991131802adcda12eb9a63005799b42a6334c600af33684bc6698c015ea6d097249318023dcda152b92630047e8ba65e224c600af53684bc4498c0197a2a6778893180337454ccd112630047e8ba656224c600ced1532ac4498c011fa2e994889318033d454c89112630067c8a98ce224c600fb82e4992e298c017e42cd7450531803f48b22c6a0a63007f81424c9414c6008ef576d293018c0196e65da421c31802abcda9313b863005379b829d950c600acf36c53b2a18c015ce6d0a765431802bb4d914eca863005739b421d950c600caf5553bb2a18c0199eaaa66654318023bc5d5332a86300573abb656440c600ea74eecac8818c01d8e9999591031802bad5db2b1986300765a66656330c600aed576cac4418c01d5a9dd95888318023ecdcd54988630047f1b9aa9310c6008df36d5532e90c011be2e997999218021fc5c352aa24300477abb6949348600caf4eed292690c01fb058d624c5218027e95d946cc423004fb1b429d83846009ee36a5490708c013dcaeda520e118025f85c55439c230063f1a96a073846009f6368540e708c013f86c8a81ce118027f15db4439c23006de1736887384600cfc352d10e708c01af86a1a21ce11803770d334439c23006f61a56887384600df4348d10e708c017e46d0a88ce118027e85d33119c23005dd0b76623384600bf236843c6708c017d46d4838ce11802de8dc0e719c23005f51b51ce3384600bf836439c6708c013bc6d8a364a118027b8da946c1423004fb1b42a172846009de36c51ae508c013dc6d4a35ca118027d8da146b9423004fd0b369d42846009be36e51a8508c013dc6d4a350a118027f05d2e499423005fa1b421e2284600fb44ef2244508c01fc89564488a11802f70db12711423004fe0ba60e2284600bec36a41c4508c016f86e07388a11802f70db0e711423005f61b51ce2284600bf436839c4508c01f709de3388a11803f613346711423007f42558ce2284600ff048919c4508c011ee2ea4464e1180237d5db4c49c23006679a695493846008df36c54aa708c015f26c8a98ce11802be4d912f19c23005f91b428633846008fd36454c6708c013dc6d4a3606118025f85c34aa0c23004f71b528d41846009fc3655526308c013bc6d8a94c6118027d8da14e98c23004fe0ba88931846009ee576d286308c01b5c9dda50c611803798d2c8818c23006f51a58cc3184600 else (if i < 2 then 0xcb74eed2126b94019ce955a424d728023f95db4249ae50065f277684935ca00cee4aad0926b94011ee6d0a960d72802e6cdb126b9ae5005d59b524d735ca00adb36c49ae6b94015d66d4935cd7280237cdb152a9ae50047b9b42a5535ca008f7576d2122b940196e9dda42457280339d2ab4848ae50047f1b12a29958a009f536851ae4b14013f86c4a35c9628027745d2c6b92c5007cc97358d7258a008f7576d2122b14019ce69644245628023ed5db4648ac500675a5568c9158a00cf3488d1922b14019da69572245628033e4d1ae448ac5007d497354d7254a008fb3675532ea14015762cd979dd42802bac59b2f2aa850047b8ba65d8450a00af3166cbb08a14015e62cd97551428022fd5db4e49a850046fabb6989350a00c9f4eed3126a14011deaeda524d428032bd3bb4a49a85006579a79549350a00ccf34d2a926a140196e69d8424d428032dcd3aa849a850047f2bb6849350a00cbe4eed0926a14019dc955a124d42802aecdb926b1a850057d1b124d6350a00abb36e49aa6a1401dc65509354d42802be459b2eb1285007e29655516250a00abd36e49ac4a14015f86c49358942803b6449ac6b1285004fc9b32856250a008f736854532994017f06c4a35c9328023bd5db4a48a65006769a55c8914ca009f5576d210f1140157a2e5a89de22802eb4da9513bc45004f69b52a27788a00bb536843cef114013ea6d0a761a228027d4da14ec2c45004fa9b429d6588a009f936653acb114013f86c4a759622802f94da10f2ac45004fa8ba6117488a00fc54cd2ac89114013ea6d0a760e228032f454ceec1c450066e8a99998388a009ed576d290711401b5a9dda520e228037353334a41c450069e9a89dc7388a009dd576d30e711401b3a9dda61ce22803574d44cc39c45004f6abb6947388a00dad4eed28e711401b9a69a551ce228036d53bb4839c45006eaa666907388a00de54aad20e711401bb2699731ce228037a4d2ae639c45004fe2bb6847388a00dbc4eed08e711401bb8999a11ce228037b12ab4239c45004f69b52a16388a009ed36a53ac7114013ea6d0a758e228027f0d894eb1c45004ee9b629d5388a009f536853aa7114013f86c4a754e228026f45bb4ca9c45005f89b42a23388a00bf136843c6711401f9299a558ce22803f453348919c45007f0a559123388a00bf136850c67114013ea6d0a88ce22802be45cb0719c4500477abb6949360600af336854c66c0c015e66d0978cd818023dcda15319b030047b9b42a57260600af53684bc44c0c011fa6caaa64c81802bccda153199030047e8ba64e2220600aaf36a54ceea0c011de6d4a99dd418021fd5d950caa83004eb9b628d74506009f536451ae8a0c011deaeda524d418032bd3bb4a49a8300667a6669493506008ef36a54ac6a0c014f62e1958cd4180 else 0x27f0d8946a12410045fabb69c91482008ef576d29229040195e69e552452080333cd34aa48a410047babb6909148200ce74aad21229040196e69e442452080335cd348848a41006739a591091482008fb576d1922904019d6955a3245208033cd2234648a410066e9a65c89148200ced34ab9122904019f268d7224520803374d328448a410067c9a35089148200ade36c48ae2904015dc6d4915c520802be8d9922b8a410075e17224571482009ed36a51a42904010ef6d0a865d20802dd6da150b92410057e4b165972482008f717522326884011fa2e993889108027b8da942982210056d9b629d9304200aeb36a53b26084015e66d0a764c10802be4d914ec98210047b9ba6507304200ce734aca0e6084019d6695931cc108033ccd2326398210065e9976887304200ced32ad10e6084019ea651a21cc108033e4c9b44398210067b1946847304200cfa326d08e6084011fa6e87364810802b74db0e6c9021005769b51cd9204200af536839b24084015f86c47364810802af55db2f110210057cabb64e22042008ef576d2926c24011eeaeda425d83802b3cdb14eca907005739b429d9520e00aed36453b2a41c015dc6c4a765483802b9cda10eca907005759b321d9520e00ae7576cac8841c011ee6d0a8a65738026dcda14ec1ae70047f2bb684981ce00ae7576cac8839c011f66e6aa5cc738033ad5532ab98e700771995911731ce00ced5552ab2439c01dca9564464873802af55dae6c90e700756a555cd921ce00cf65552232239c01dcc95644644738031f955330c88e70067b2aa651911ce00cfc554c932239c011ee6d0a8a65538023dd5db484baa70047eabb6889754e008fe576d092ea9c011deaeca961553802b3cdb12ec2aa7005679b625d5454e00ae7172ba2a8a9c015ae6d89791153802bd4d912f222a70057b1b125e4454e00bb33684bae6a9c017726c8975cd53803e8cba2a8b9aa70055b9b425d7354e00abd3644bae6a9c013e6aeda4262338039cc4c328c2467004f99b42a1928ce009f336850b2519c013e6aeda4246338023dcda150cbc670047b9b42a5858ce00ae73684c4ab19c013e66d0a960e338027ccda14ec1c670047b9b42a5838ce009db576d30e719c013d6aeda51ce3380372cd34aa39c67006d9a77690738ce00de34aad20e719c01b729dda21ce338037a52ab4439c67004fd2bb684738ce00dba4eed08e719c01bd4955a11ce3380276cdb14ea9c67004f99b429d538ce009f936453aa719c013f46c4a754e338023dcda150c946700673a55690918ce008ef576d2926c140195e9dda524d828023bcda9514cae50047babb690985ca00ab73684c4eeb94011ee6d0a961572802b9cda1312aae50046fabb698935ca00c9f4eed3126b94011deaeda524d728032bd3bb4a49ae5006679a6954935ca0)) else (if i < 5 then (if i < 4 then 0xcf9b46b9122b14019fa5c9a0245628031bea8b464c2a5004b7db52a27754a0087fb72542e6a94010ff6e4a858d528025beda950b1aa5005b5cb85cd5354a00977b6854466a94016eb6d0a85c9528038f64c2e6b92a5007d4d7354d7254a0096fb6a544eea14014e72cd976114280317e5c34c49a850061bda76109350a00c77b4ec2126a14018ee611a024d428038decbb08b9a85004b7db52a16350a0097db64542c6a14014bf2e19658d42802aeedb926b1a8500739d8424d6350a00af9966cbac4a1401ceb65d8458942802af6db926b12850073ad8424d6250a00f55b08b1ac4a1401db324d63589428021deda1514ca650069ed71688874ca0087f974c3b2c994012df6d4a858d328029f65c32cb92650053ecb8655724ca00d75b4ec228499401ceb65984509328033b6d2ae448a65004b6db52a27788a00c5d95333307114012db6d4a858e228025d6da15119c450043bdb42a57260600d7cae450ac4c0c012fc6c0a1589818021f6d9554c990300637da56507320600c7db2ad10e640c018fb651a21cc818039aecaae6a99030053edb21cd9020600a77b6843b2440c0166f6cc875d14180275edb146ba283004fadb228d7450600c5f930d30e6a0c018df261a51cd418031f64c34439a83005abcb859163506009b7b6e51a84a0c013af6d8a350941803cdaba2e640a83005af5b61cc8150600b6eb6a39902a0c016f96c873205418021f6d91514ca63004b7db52a2774c600c77952c22e898c013b76d8a35d1318035cec2146ba263004fcdb228d744c60097bb64542c698c016d76d4a858d31802d6e5c2c8b1a63004b7db52a1634c600a6fb6a4c2a698c015eb6d097249318039da4c2e8a0a63005f94b35d1414c600c37b2ed210e18c014cf6d08765431802abcdb940ca863005679b6281950c600ae73685032a18c015da6c8a0654318038decbb08ba06300733d95611740c600c77d32d210e90c012df6d4a89dd218025beda950b1a43004bbdb42a23348600c7d930d10e708c014fb6c8985ca118029f65c324b94230047eabb688974c200af53644b928984011fa6c8a95d1308031dc54b08ba2610047b8ba65e444c200af53644bc88984019ae2a66691130802af4d912eb9a61006b99a4612334c2009eb36a51ae4984013e66d0a35c9308027e8d8946b92610057a8b9912224c2008ef576d2922984019ce69644245308033acd2c6648a61006739a5250914c2008f7172d20e2984011de6d4a950530802b755db2d110610066b996690710c2008ef174cbcaa904015ec2c596911208023dc5d488c9a410046fabb6989348200ccf34d2a926904015f82c5965c9208027b4da946b9241004fa9b428d72482009fc36251ae4904012fa2e9835c9208027e459b4ea12410057e0b165942482009bd36e51a84904013da6d4a3509208 else 0x95d4a6a4f525a928491a47923291448223fd1f48f547823ad1cc8e1468a3051788b7459228913a898449a23911288443fa1e90ea870435a1990c285c426211d08483d416a0a104681340720250087ff3fd1fd4fe07eb3f31f84fb87cc3e39f08f7a7b83d41e60f2678e3c49de4ed27593a49ce4e6872f3951c94e407103801bc0dc06db36b1b18d6c6a63509a70d2e6923469a20d066733319978cb265432218d0c4861430217d0bc85d42e216d0b4859f2cd1628b0a5802bd95d8ae256c2b39588aba5582a99538a9254429f94e8a6a5302959498a4251c28b9448a1a50828193f89f24f427793a89ca4e026d93589a24cc263930897a4b825992b89524a424f926892a490245921890247c23611708ae44722110f4870428211904c8063fe1fc8fd07c83df1ed0f287743aa1cd0e2870a3751b28d546a034b1a30cd86623211888bd85cc2e116e0b5c5a42c21590ab45502a314f0a6452828f1450a144ea26512a8914480230115886c4161fb0f5876c3ac1d10e6071c3841bd0dc06cc35c1a90d2067c31e18a0bd05d42e01600ad85582a214c0a3850827a13809984b825212408f846822a11008584182020fc07b83c81da0e807183781b20d4067832818a0c005d82d81620ac053828813a098049823811208403f81e80ea07003581980ac051026011c06e03201680a004601e00c805001e00a00280031bed2acacb90700527db629d9520e00a6fb6c53b2a41c014cf6d0a7654838029b6d914eca907005375b129d9520e00a6f36053b2a41c014dfaeda6654838031bed3b4cca90700537db66859520e00c6fb4cd0b2a41c014df6d8a1654838029bedb10eca90700533db421d9520e00a6bb6643b2a41c018df615a5a65738029f65c34cc90e70057b1b4281911ce00afc3645032239c018df699a5261538031bea8b444c2a7004b7db56849854e00c3f93053b2ca9c0149f6d897615538029bcd812ec2aa7005a7db625d8554e00b67b684bb0aa9c016db6c89761553802dbad892ec2aa7005b79b025d8554e0096f974cb30aa9c0165f2dd9661553802cee5bb2c41aa7006b5d752a17354e00b6bb6a542e6a9c012df6d4a85cd538031f6b13444c4670043bdb42a1928ce00877b685432119c018f758ca95cd828021beda9514cae500637d65694985ca00877d76d2130b940186f9dda4261728031ded33484c2e50053bdb4261965ca00a77b684c32ab94010ef6d0a9615728029bedad32c2ae50053bdb4261755ca00a67b684c4aab94016e72cd946117280317e5c34c49ae50043bdb42a5835ca0096fb6a542c6b94012fb6c8a858d7280237edb152a9ae500637ca9615535ca00f2bb0ab9aa6b94014ef6d09864572802dd6da150b92c5004fadb428d7258a0097d974c1ae4b14013bb2e9635c962803e66b9ac6b92c500676da55c89158a) else (if i < 6 then 0xf47b0044961334004c00d2584000420d47c1c40c50106280802b86140271000504000400024b08500828004140034002006e3634c47638016006000001b21000003c203f8008000027080fd0fc00603c203c200001d1c20074700a268e1000508270f4709000e0d080028400300130013001300100a100a10000000010800e1c2e1c200000006870b50d0e200c10000050419041f0e10300080000008107038703840304181c2408381c381c2018200000000000000080828082808280828082b8c01080104010601070384140020000180038003800380034003400340034002c002c002c002c002c002c003800380038003800380020000182c382c382c382c340034002000210000000000000000000004200001a003e1c3e1c2000000f0e100000000000432002000240040000000000000000000210000004200480080000000000000900100000e0e1e0e10000004381c381c381c381c200000040414041c0e1e0e1001400740078384000000005800f0708000e0e1e0e1e0e1e0e1c0e1c0e1c0e1c0e1c0e11041002100101040000000000000000000000000000000000000000000000000000000000000000000a001a001060208000f0e107870b8708000f0e10000107438743874384810400042004200c200000184000c3e1c2e1da388008400003438743840000000000061c3e1c3e1c261c2000a101800e020e020e0208050800000000000000003080008400a0e10000000000000000000000000000000000000000000000000000000000000028104000502080000000000000afa573ab935c4ada56beb13584aba55beabf55aaaad542a81530a95d46ea17506a80d3c69c34c6a505242901470a305142881430a15d09a82d4069fb4fc67d93e79f14f4a7853b29d6cea274739e9c74e266f33749b7ccfa6733299924c7e63530a97d4b7e59f2bf957caaa54b2a094dca2e50d281938c9b24cf257929493649122290ec7b23b91b68d3468632318c8b8c5b22b91578a3c50a265117889440a1e50ed874438e1a70c385f42ba153099844c2120ff038819c0ba05302480a403e0150057fabf69faafd07e5beedf2af857babdc1ed6f667b0bd45e98f477963c71e2ef0777bbb9ddaeec77613ac9d5aea874c3a21cf0e6872c3921c86e3e71cb8d1c5ee1f70d3855c0adf56f837adbccde16ee375db8edac6ce365db24d8d6c435e1ad0d586a9b50da7cd3969a34bda54d1a68533e99d4ce566ab31596aca564ab241916c86640b1f18eec72636b1a18c6c5e62cb125872c2960cb0257dcbde5e72ef975cba95ccae5171eb8a5c2add56cab555a2acd564ab15582abd55caad5562aad554aa95542a9d54caa55528292d48ca41518a885422a014f8a7853b89cc4e3a70937a9b84d9a6b93529a44cfa66932a9904c5a6193029714b6259d2c4 else 0x46103b857800c0003a1001400a004603c61000508000a22100210180098008002002c2c25ab4008028015003c161c161c161c16100211001c161001ac844004008400000008540054004000000084120020042d043d1e40100004200037187b1871408b10240c280c28080000001080000420075908000297d1f400c166925)))
def l3853r8 : Packing := (586,5,6,0,0,13,0,p3853r8)
def p3853i8 (i : Nat) : Nat := 0xf0dc7000cd0020c952ab2024544802e26d10000fc5400f18811432cf4ec4b2c00c218e0034a03006a20
def p3853r9 (i : Nat) : Nat := (if i < 17 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x3284600bfc69d3284600bfc29d3284600f7c9dd3284600bfc6993284600bfc6953284600bfc6913284600ff424d3284600ff48cd3284600ff85c93284600ff85093284600ff82622284600ff825e2284600ff861e2284600ff821e2284600f789de2284600ff89de2284600ff861a2284600ff85da2284600fb899a2284600ff86162284600ff85d62284600ff85962284600fd89562284600ff86122284600ff85d22284600ff85922284600ff85522284600fe89122284600ff824e2284600ff860e2284600ff820e2284600ff85ce2284600ff81ce2284600ff858e2284600ff854e2284600ff850e2284600ff08ce2284600ff88ce22846009fe69098846009fe68c98846009fe68898846009fe2a194846009fe2a58484600dee2624484600dee6564484600fce95644846009fe2a19384600dde9559384600dee91193846009fe69c93846009be69893846009fe69893846009fe6949384600dde95493846009fe6849384600bbe6989384600bfc68493846009fe2a58384600bde6948384600bfc68483846009fe2a57384600afe6a07384600bee6907384600bfa6887384600bfc68473846009fe2a55384600df62a63384600df62623384600df665e3384600df625e3384600f769de3384600df66563384600fd69563384600df66523384600fe69123384600ff46863384600ff428633846009fe2a63384600df664e3384600bfc68633846009fe2a19284600d7e9dd9284600dde9559284600dee9119284600df68cd92846009fe2a58284600cfe26182846009fe2a57284600d7e25d7284600dfa64972846009fe2a55284600dfa6494284600dfa2622284600dfa25e2284600f7a9de2284600fda9562284600fea9122284600ff28ce2284600bfc2a58184600bfc28d8184600ff48cd8184600ff888981846009fe2a58184600bfc6908184600fec9108184600bfc68c8184600ff48cc8184600bfc2a14184600dfc2614184600bfc29d4184600f7c9dd4184600fbc9994184600bfc6954184600fdc9554184600fec5d14184600fec5914184600bfc28d4184600dfc64d4184600ff48cd4184600fec5094184600ff88894184600bfcaa93184600bfc2a53184600bfc2a13184600bfc69d3184600bfc29d3184600dfc65d3184600f7c9dd3184600fbc9993184600bfc6953184600fdc9553184600bfc6913184600dfc6513184600fec9113184600ff420d3184600ff458d3184600ff48cd3184600ff82893184600dfc6493184600ff44c93184600ff88893184600bfc69c3184600f7c9dc3184600bdc6943184600bfc6943184600fdc9543184600bfc6903184600fec9103184600ff48cc3184600bfc69d2184600f7c9dd2184600bfc6952184600fdc9552184600bfc6912184600fec9112184600bfc68d2184600ff48cd2184600 else 0xdde95594486009fe6a574486009fe6a564486009fe6a55448600deea664448600dee2624448600dee65e4448600dee25e4448600f6e9de4448600dee65a4448600fae99a4448600dee6564448600fce95644486009feaa993486009fe2a19348600d7e9dd9348600dbe9999348600dde9559348600dee91193486009fe69c9348600d7e9dc93486009de69493486009fe6949348600dde95493486009fe6a48348600bde6948348600bfc68483486009fe6a573486009fe6a47348600afe6a07348600bbe6987348600bde6947348600bee6907348600bfa6887348600bfc68473486009fe6a563486009fe6a55348600dde65553486009fe6a54348600df62a63348600df6a663348600df62623348600df665e3348600df625e3348600df665a3348600fb699a3348600df66563348600fd69563348600df66523348600fe69123348600ff42863348600df664e3348600dfa65d6248600f7a9dd6248600fba5956248600fda9556248600dfa6516248600fea9116248600fba58d6248600ff28cd6248600bfcaa93148600dfca653148600dfc65d3148600f7c9dd3148600fbc9993148600fdc9553148600dfc6513148600fec9113148600ff420d3148600ff458d3148600ff48cd3148600ff85893148600bf428d9884600bfc28d9884600bfcaa89884600bfc68c9884600bfc6889884600bfc2a58384600bfc29d8384600bfc2a48384600bfc69c8384600bfc6988384600bdc6948384600bfc6948384600fdc6948384600bfc6908384600ff424c8384600efc60c8384600bfc6888384600bfcaa97384600bfc2a17384600bfcaa87384600afc6a07384600efc6a07384600bfc2a07384600ff45cc7384600bf86887384600bfc6887384600ff86887384600ff46a23384600ff42a23384600ff46623384600ff42623384600ff469e3384600ff429e3384600ff461e3384600ff421e3384600f749de3384600ff46963384600ff468a3384600bfc69e3384600bfc29e3384600bfc6963384600ff460e3384600ff420e3384600ff45ce3384600ff41ce3384600bfc68a3384600bfc2a19284600bfc29d9284600f7c9dd9284600bfc28d9284600ff48cd9284600bfc2a58284600efc2618284600bfc29d8284600f7c9dd8284600bfc28d8284600ff48cd8284600bfcaa97284600bfc2a57284600bfc2a17284600f7c25d7284600f7c9dd7284600bfc28d7284600f7c5cd7284600ff48cd7284600ff86497284600ff48cd6284600ff85c96284600bfcaa95284600bfc2a15284600bfc28d5284600ff48cd5284600ff85c95284600bfcaa94284600bfc2a14284600bfc69d4284600bfc29d4284600f7c9dd4284600bfc6954284600bfc28d4284600ff48cd4284600ff86494284600ff85894284600bfcaa93284600bfc2a53284600bfc2a1) else (if i < 3 then 0xd414c600fbc999414c600fdc955414c600fec5d1414c600fec591414c600ff428d414c600ff420d414c600ff458d414c600ff48cd414c600ff8249414c600fec509414c600ff44c9414c600ff8889414c600bf628d414c6009fe2a2990c6009fe69c980c6009de694980c6009fe694980c6009feaa9970c6009fe2a1970c6009fe68d970c6009ee690970c6009fa688970c6009fe6a4870c600d7e65c870c600bee690870c600d7ea66770c600d7e262770c600d7e65e770c6009fe6a5760c600d7e65d760c600dbe659760c600dbe65e660c6009deaa9950c600ddeaa9950c600dde6a1950c600dde2a1950c600dde69d950c600dde29d950c600dde61d950c600dde21d950c600d5e9dd950c600dde9dd950c600dde699950c600dde619950c600dde5d9950c600d9e999950c600dde691950c600dde689950c6009feaa9950c6009fe2a1950c600d7e9dd950c600dbe999950c600bdeaa9950c600dde661950c600dde65d950c600f5e9dd950c600dde655850c6009fe6a5750c600dde655750c6009fe6a5650c600dde655650c600ddea66550c600dde262550c600dde65e550c600f5e9de550c600dde65a550c600f9e99a550c600d7e9dd940c600dbe999940c600dde955940c600dde655840c6009fe6a5740c600d7e65d740c600dde655740c600dee651740c6009fe6a5640c600dbe659640c600dde655640c600dee651640c6009fe6a5540c600dde655540c600dee65e440c600f6e9de440c600dee65a440c600fae99a440c600dce656440c600dee656440c600fce956440c600dde655830c600dde655730c600dde655630c600dde655530c600df665e330c600df665a330c600fb699a330c600dd6656330c600df6656330c600fd6956330c600d7e9dd920c600dde955920c600dde655820c6009fe6a5720c600d7e65d720c600dde655720c600dfa649720c6009fe6a5520c600dde655520c600dfa65e220c600f7a9de220c600dda656220c600dfa656220c600fda956220c600dde655810c600dde655710c600dde655510c600dde655410c600bf6aa9310c600fd6955310c600fe6911310c600bfcaa9310c600dfc65d310c600f7c9dd310c600fbc999310c600fdc955310c600dde655310c6009fe2a299486009fe69c98486009fe69498486009fe69098486009fe68c98486009feaa997486009fe2a19748600dbe29997486009fe69097486009fe68c97486009fe6a48748600bee6908748600d7e2a67748600d7ea667748600d7e2627748600d7e65e7748600dbe65e6648600f3e9de66486009feaa995486009fe2a19548600d7e9dd9548600dbe99995486009fe6a57548600ddea665548600dde2625548600dde65e5548600f5e9de5548600f9e99a55486009feaa994486009fe2a19448600d7e9dd9448600dbe999944860 else 0xbf628d874c6009fe6a4874c600bee690874c600bfc684874c600d7ea66774c600d7e262774c6009fe2a6774c600bfc286774c6009fe2a5864c600bf628d864c600dbea66664c600dbe262664c6009feaa9954c6009fe2a1954c600d7e9dd954c600dbe999954c600dfa289954c6009fe2a5854c600bf628d854c600ddea66554c600dde262554c600f5e9de554c600f9e99a554c6009feaa9944c6009fe2a1944c600dbe999944c600dde955944c600dfa289944c6009fe2a5844c600bf628d844c6009fe6a5744c6009fe2a5744c600dee651744c600bf628d744c6009fe2a5644c6009fe6a5544c600deea66444c600dee262444c600dee65e444c600dee25e444c600f6e9de444c600fae99a444c600dee656444c600fce956444c6009fe2a5834c600cfe261834c600bfc285834c600bf6aa8834c600df6a64834c600f769dc834c600bf6698834c600fb6998834c600fd6694834c600df6654834c600fd6954834c600df6650834c600fe6910834c600bf6688834c600bde694834c6009fe2a5734c600d7e25d734c600bfc285734c600afe6a0734c600bbe698734c600bde694734c600bee690734c600bfa688734c600bf6aa9634c600df6a65634c600bf62a1634c600fb65d9634c600fd6955634c600fb6591634c600fe6911634c600ff4285634c600bfc285634c600bfc285534c600df62a6334c600bf62a2334c600df6262334c600df665e334c600df625e334c600bf669a334c600fb699a334c600df6656334c600fd6956334c600df6652334c600fe6912334c600bf668a334c600dfaa64924c600dfa260924c600dfa65c924c600dfa25c924c600f7a9dc924c600dfa658924c600fba998924c600dfa654924c600fda954924c600dfa650924c600fea910924c600ff220c924c600ff258c924c600ff28cc924c6009fe2a5824c600bf628d824c6009fe2a5724c600d7e65d724c600fb658d624c6009fe2a5524c600dde655524c600dee651424c600bf6aa9324c600df6a65324c600bf62a1324c600bf6699324c600fb6999324c600fd6955324c600fe6911324c600ff25c9324c600ff2509324c6009fa2a6224c600bfa2a6224c600dfaa66224c600dfa262224c600dfa65e224c600dfa25e224c600f7a9de224c600fba99a224c600dfa656224c600fda956224c600dfa652224c600fea912224c600ff220e224c600ff258e224c600ff28ce224c6009fe2a5814c600cfe261814c600bf628d814c6009fc2a5714c600dfc2a5714c600dfca65714c600fec911714c600ff428d714c600ff420d714c600ff48cd714c600ff8249714c600f7c5c9714c600ff44c9714c600ff8889714c6009fe6a5714c6009fe2a5714c600bf628d714c600bf628d514c600bfcaa9414c600dfca65414c600dfc261414c600bfc69d414c600f7c9d)) else (if i < 6 then (if i < 5 then 0x562220600dfa6522220600fea9122220600dfa64e2220600ff28ce2220600ef68cd81206009fe2a299506009fe69e99506009fe69a99506009fe6969950600dee69299506009fe68e99506009fe68a99506009feaa898506009fe69c98506009fe69898506009fe68c98506009fe68898506009fe68c97506009fe6889750600d7e65c97506009fe6a48750600bee6908750600d7e2a67750600d7ea667750600d7e26277506009fe2a67750600dbea666650600dbe2626650600f3e9de66506009feaa995506008fe2a19550600cfe2a19550600afe2a19550600ddea665550600f5e9de5550600f9e99a5550600beeaa974506009ee2a57450600deea657450600bee2a17450600f6e25d7450600f6e21d7450600f6e9dd7450600fae9997450600fce9557450600bee28d7450600fec2857450600beeaa96450600deea656450600bee2a16450600bee69d6450600f6e9dd6450600fce9556450600bee28d6450600fec28564506009fe69c9350600d7e9dc93506009fe6989350600dbe99893506009de69493506009fe6949350600dde9549350600bde6949350600df664c93506009fe6a48350600bde6948350600bfc68483506009fe2a57350600f6e5d173506009fe6a47350600bbe6987350600bde6947350600bee6907350600bfa6887350600bfc68473506009fe2a56350600fae59163506009fe2a55350600dde6555350600df62a63350600df6a663350600df62623350600df625e3350600fb699a3350600df66563350600fd69563350600fe66923350600fe65d23350600fe65923350600ff428633506009fe2a63350600bee6923350600bfc28633506009fe2a57250600bfc28562506009fe2a55250600beeaa94250600deea654250600bee2a14250600bee69d4250600f6e9dd4250600bee6994250600fae9994250600dee6554250600fce9554250600bee28d4250600fe68cd4250600fea5894250600fea5093250600dfaa662250600dfa2622250600dfa25e2250600f7a9de2250600fba99a2250600dfa6562250600fda9562250600fea5d22250600fea5922250600ff28ce2250600bfcaa88150600dfca648150600f7c9dc8150600fbc9988150600fec5d08150600fec5908150600bfc68c8150600ff48cc8150600fec5088150600ff888881506009fe2a2994c6009fe69e994c6009fe69a994c6009fe696994c6009fe692994c600df668e994c6009fa68a994c6009fe68a994c600dfa68a994c600dfc686994c600bfa68a994c6009feaa8984c6009fe69c984c6009fe698984c6009fe694984c6009fe690984c6009fe688984c600cfe660984c600bf628c984c6009feaa9974c6009fe2a1974c600dfa289974c6009ee690974c6009fe690974c6009fe688974c600d7e65c974c600bee690974c6009fe2a5874c6 else 0xa00fea6117488a00bfaaa96488a00bfa2a16488a00bfa69d6488a00bfa29d6488a00f7a9dd6488a00fda9556488a00fea5d16488a00bfa69d5488a00f7a9dd5488a00bfa6995488a00fba9995488a00fda5955488a00fea5d15488a00fea21e4488a00fea9de4488a00fea5da4488a00faa99a4488a00fea5d64488a00fea5964488a00fca9564488a009fa2a58388a00bfa29d8388a00f7a9dd8388a00fba9998388a00bfa69c8388a00f7a9dc8388a00bfa6988388a00fba9988388a00bda6948388a00bfa6948388a00fda9548388a00bfa6848388a00bfaaa97388a00bfa2a17388a00f7a9dd7388a00fba9997388a00fda9557388a00f7a5d17388a00fea9117388a00afa6a07388a00f7a9dc7388a00bba6987388a00bfa6987388a00fba9987388a00bda6947388a00bfa6947388a00fda9547388a00bea6907388a00ff25cc7388a00bf86847388a00bfa6847388a00bfaaa96388a00bfa2a16388a00bfa69d6388a00bfa29d6388a00fba5d96388a00fda9556388a00fba5916388a00fea9116388a00ff25cd6388a00bfaaa95388a00bfa2a15388a00bfa69d5388a00bfa29d5388a00bfa6995388a00fba9995388a00fda6155388a00fda5d55388a00fda5515388a00fea9115388a00ff220d5388a00ff25cd5388a00bfa69d4388a00bfa6994388a00fba9994388a00bfa6954388a00fda9554388a00fea5d14388a00ff22a23388a00ff261e3388a00ff221e3388a00ff261a3388a00fb299a3388a00ff26163388a00ff25963388a00fd29563388a00ff26123388a00ff25923388a00ff25523388a00fe29123388a00ff22863388a00bfa2a23388a00bfa29e3388a00fba99a3388a00fda9563388a00ff260e3388a00ff25ce3388a00ff258e3388a00ff254e3388a009fe69c93606009fe69893606009de69493606009fe2a57360600bee6907360600bfa6887360600bfc6847360600df62a63360600df625e33606009fe2a633606009fe2a57260600bfc2856260600dfa25e2260600f7a9de2260600fba99a2260600ff28ce22606009feaa99420600deea6644206009feaa99320600dde9559320600dee9119320600dfa28993206009fe6a48320600bde6948320600df664c8320600bfc68483206009fe6a573206009fe6a47320600bee6907320600bfa6887320600bfc68473206009fe6a55320600dde65553206009fe6a54320600df62a63320600df6a663320600df665e3320600df66563320600fd69563320600df66523320600fe69123320600df664e3320600d7e9dd9220600dde9559220600dee9119220600df68cd92206009fe6a57220600d7e65d72206009fe6a55220600dde65552206009fe6a54220600dee65142206009fe6a53220600df664d3220600dfa65e2220600f7a9de2220600dfa6562220600fda9) else (if i < 7 then 0x9de5550a00dde65a5550a00deea658450a00dee65d8450a00f6e9dd8450a00deea655450a00dee65d5450a00fce5955450a0097e69c9350a009fe69c9350a00d7e9dc9350a009be6989350a009fe6989350a009de6949350a009fe6949350a00dde9549350a00dee6109350a00dee5509350a009fc6849350a009fe6849350a00d7e65d7350a00dbe6596350a00df624d6350a00dde6555350a00fce5515350a00df624d5350a00dee65d4350a00bee6954350a00fce9554350a00df665a3350a00df66563350a00fe66123350a00fe65523350a00bfaaa96250a00dfaa656250a00bfa2a16250a00dfa65d6250a00f7a9dd6250a00fba5956250a00fda9556250a00fea6116250a00fea5516250a00dfa24d6250a00fba58d6250a00fea50d6250a00ff28cd6250a00bfa2856250a009fe69c9150a00d7e9dc9150a009fe6949150a00dde9549150a009fe2a2994ca009fe69c984ca009fe698984ca009fe694984ca009fe684984ca009feaa9974ca009fe2a1974ca009fe684974ca009fe6a4874ca00bee690874ca00bfa688874ca00d7e65e774ca009feaa9964ca009fe2a1964ca009fe6a5764ca009feaa9954ca009fe2a1954ca009fe6a5754ca009fe6a5654ca00ddea66554ca00dde262554ca00dde65e554ca00dde65a554ca00dde955944ca009fe6a5744ca009fe6a5644ca009fe6a5544ca00dee65e444ca00dee65a444ca00dee656444ca00fce956444ca00df665e334ca00df665a334ca00df6656334ca00fd6956334ca00bfaaa9724ca009fa2a5724ca00dfa2a5724ca00dfaa65724ca00dfa261724ca00f7a9dd724ca00dfa659724ca00dfa655724ca00fda955724ca00fea911724ca00ff228d724ca00f7a5cd724ca00ff28cd724ca00bfa69d424ca00dfa659424ca00fda955424ca00fea611424ca00fea551424ca009fe69c914ca009de694914ca009fe694914ca00dde954914ca00dfa5c8914ca00bfaaa88788a00efa61c8788a00bfa6988788a00bfa6948788a00bea6908788a00bfa6908788a00fea6908788a00bfa68c8788a00bfa6848788a00f7a6a27788a00f7a2a27788a00bfa2a27788a00f7a61e7788a00f7a21e7788a00bfa69a7788a00bfa6967788a00bfa6927788a00bfa68e7788a00bfa6867788a00bfa29d8688a00f7a9dd8688a00bfaaa97688a00bfa2a17688a00f7a9dd7688a00bfa29d8588a00f7a9dd8588a00bfaaa97588a00bfa2a17588a00f7a21d7588a00f7a9dd7588a00bfaaa96588a00bfa2a16588a00bfa69d6588a00bfa29d6588a00fba5d96588a00fda6156588a00fda5d56588a00fda21e5588a00f5a9de5588a00fda9de5588a00fda5da5588a00bfa29d8488a00f7a9dd8488a00fba9998488a00bfaaa97488a00bfa2a17488a00f7a21d7488a00f7a9dd7488a00fda9557488 else 0xca00bde694835ca00bfa688835ca00b7eaa9735ca00d7ea65735ca00f5e955735ca00f6e911735ca00f7624d735ca00df624d735ca00afe6a0735ca00bbe698735ca00bde694735ca00bee690735ca00bfc684735ca009fe2a5635ca00f765cd635ca009fe2a5535ca00f765cd535ca009fe2a6335ca00b7e29e335ca00f765ce335ca00d7e9dc915ca009fe694915ca00dde954915ca009ee690915ca009fe690915ca00dee910915ca009fe68c915ca00bee690915ca00dfc644915ca009fe2a29958a009fe6909858a009fe68c9858a00deea664458a00dee2624458a00fce9564458a009fe69c9358a009fe6949358a00dde9549358a009fe6a48358a00bbe6988358a00bde6948358a009fe6a47358a00afe6a07358a00bee6907358a00bfa6887358a00bfc6847358a00bfa68a3358a00bfaaa97258a00dfaa657258a00dfa2617258a00f7a9dd7258a00fda9557258a00fea9117258a00bfa28d7258a00f7a5cd7258a00fba58d7258a009ee6909158a009fe6909158a00dee9109158a009f668c9158a009fe68c9158a00dfa5c89158a009fe2a29954a009fe69e9954a009fe69a9954a009fe6929954a009fe68e9954a009fe6869954a009feaa89854a009fe69c9854a009fe6989854a009fe68c9854a009fe6849854a009feaa99754a009fe2a19754a009fe6909754a009fe68c9754a009fe6849754a00d7e65c9754a009fe6a48754a00bee6908754a00bfa6888754a00d7ea667754a00d7e2627754a009fe2a67754a00d7e65e7754a009fe2a57454a009fe2a56454a00deea664454a00dee65e4454a00dee25e4454a009fe69c9354a009fe6989354a009fe6849354a00df664c9354a009fe6a48354a00bde6948354a009fe2a57354a009fe6a47354a00bbe6987354a00bde6947354a00bee6907354a00bfa6887354a00bfc6847354a009fe2a56354a00bdeaa95354a00ddea655354a00dde65d5354a00fce9115354a00fd624d5354a00fd620d5354a00fd65cd5354a00df6a663354a00df62623354a00fe69123354a009fe2a63354a00fd654e3354a00bfaaa97254a00dfaa657254a00bfa2a17254a00dfa2617254a00f7a25d7254a00f7a9dd7254a00fea9117254a00f7a5cd7254a00fda54d7254a009fe69c9154a00d7e9dc9154a009fe6909154a00dee9109154a009fe68c9154a00df68cc9154a00dfa5c89154a00dfc6449154a009fe2a29950a009fe69c9850a009fe6989850a009fe6849850a009feaa99750a009fe2a19750a009f628d9750a00df628d9750a009fe6849750a009fe6a48750a00bee6908750a00d7e2a67750a00d7ea667750a00d7e2627750a00d7e65e7750a009feaa99650a009fe2a19650a00d7e9dd9650a009feaa99550a009fe6a57550a009fe6a56550a00ddea665550a00dde65e5550a00f5e))) else (if i < 12 then (if i < 10 then (if i < 9 then 0xe684978ce00bf668c978ce009fe2a5878ce00cfe261878ce00bee690878ce00bf668c878ce009fe2a6778ce009fe2a1968ce009fe2a1958ce009fe2a5858ce00dde262558ce00dde65e558ce00dde65a558ce009fe2a1948ce00dde955948ce009fe2a5848ce00cfe261848ce00dee651848ce009fe2a5748ce00d7e25d748ce00dee651548ce00dee262448ce00dee25e448ce00fce956448ce00bf62a5838ce00bf629d838ce00bf6285838ce009fe2a5838ce00bf669c838ce00bf6698838ce00bd6694838ce00bf6694838ce00fd6954838ce00bf6684838ce00bf62a5738ce00bf62a1738ce00f769dd738ce00df6659738ce00df6655738ce00fd6955738ce00f765d1738ce00fe6911738ce00bf6285738ce00af66a0738ce00f769dc738ce00bb6698738ce00bf6698738ce00bd6694738ce00bf6694738ce00fd6954738ce00be6690738ce00bf2688738ce00bf4684738ce00bf6684738ce00bf62a1538ce00df6261538ce00bf669d538ce00bf629d538ce00df665d538ce00fd6615538ce00fd65d5538ce00fd6551538ce00fe6911538ce00bf6285538ce00df6261438ce00bf669d438ce00bf6695438ce00fd6955438ce00fe65d1438ce009fe2a1928ce00dde955928ce009fe2a1918ce00dde955918ce009fe69c918ce009fe694918ce00dde954918ce009ee690918ce009fe690918ce00dee910918ce00bee690918ce00bf668c918ce009fe68c9760a009fe6849760a00d7e2a67760a009fe2a67760a009fe69c9360a00d7e9dc9360a009fe6989360a009de6949360a009fe6849360a009fe2a57360a00bbe6987360a00bde6947360a00bee6907360a00bfa6887360a00bfc6847360a00df62a63360a00ef62a23360a00df625e3360a009fe2a63360a00afe2a23360a009fe69c9160a00d7e9dc9160a009fe68c9160a00df68cc9160a009fe2a2995ca009fe69a995ca009fe696995ca009fe692995ca009fe68e995ca00dfa68a995ca009fe686995ca00bf628d985ca009feaa8985ca009fe698985ca009fe694985ca009ee690985ca009fe690985ca00dee690985ca009fe68c985ca009fe684985ca00cfe660985ca00bee690985ca00cfe261875ca00bee690875ca00d7e262775ca00b7e68e775ca00b7e686775ca009fe2a5865ca00b7e29d865ca009fe2a5855ca00ddea66555ca00dde262555ca00f5e9de555ca00bf628d945ca009fe2a5845ca00deea66445ca00dee262445ca00f6e9de445ca00fce956445ca00d7e9dc935ca009be698935ca009fe698935ca009de694935ca009fe694935ca00dde954935ca009ee690935ca009fc684935ca009fe684935ca00afe6a0935ca00bbe698935ca00bde694935ca00bee690935ca00df664c935ca00bfc684935ca009fe2a5835ca009fe6a4835ca00b7e69c835 else 0x1ce00dde955921ce00cfa661921ce00dfa661921ce00dba659921ce00dda655921ce00dea651921ce009fcaa9911ce00dfcaa9911ce00dfc6a1911ce00dfc2a1911ce00dfc691911ce00dfc611911ce00dfc551911ce00dec911911ce00dfc60d911ce00dfc5cd911ce00dfc689911ce009feaa9911ce009fe2a1911ce00dee911911ce00bfcaa9911ce00cfc661911ce00dfc661911ce00dec651911ce00df8649911ce00cfe661911ce00dee651911ce00dfa649911ce009fe2a29954e009fe69e9954e009fe69a9954e00dde6969954e009fe6929954e009fe68a9954e009fe6869954e009feaa89854e009fe69c9854e009fe6989854e00dde6949854e009fe6889854e009fe6849854e009be6989754e009ee6909754e009fe6909754e009fa6889754e009fe6889754e009fc6849754e009fe6849754e00d7e65c9754e00bbe6989754e00bee6909754e00bfa6889754e00bfc6849754e009fe6a48754e00bde6948754e00bee6908754e00bf668c8754e00b7e29d9654e009de2a58554e00ddea658554e00ede2618554e00dde25d8554e009fe2a57454e00ddea655454e00dde25d5454e00fce5d15454e00deea664454e00dee25e4454e00bf6aa88354e00df6a648354e00bf669c8354e00fd66948354e00bde6948354e00bf6aa97354e00df6a657354e00bf62a17354e00f7625d7354e00fd66157354e00f765d17354e00fd65517354e00fe69117354e00d7e25d7354e00bbe6987354e00bee6907354e00bfa6887354e00bfc6847354e009fe69c9154e009fe6909154e00dee9109154e00dfc6449154e009fe2a29950e009fe69c9850e009fe6989850e009fe6849850e009feaa99750e009fe2a19750e009fe6849750e009fe6a48750e00bee6908750e009feaa99550e009fe6a57550e00ddea665550e00dde65e5550e00beeaa97450e009ee2a57450e00dee2a57450e00deea657450e00f6e21d7450e00dee6557450e00fce9557450e00fe628d7450e00fe65d08350e00f6e5d17350e009fe69c9150e009fe6949150e00dde9549150e00bf6285988ce00bf6aa8988ce00bf6698988ce00be6690988ce00bf6690988ce00fe6690988ce00bf6688988ce00bf6684988ce00bf62a5848ce00ef6261848ce00bf629d848ce00fe6651848ce00bf6285848ce00fe6262448ce00bf62a1928ce00bf629d928ce00bf6285928ce00bf62a1918ce00df6261918ce00bf629d918ce00bf669c918ce00bf6698918ce00bf6694918ce00be6690918ce00bf6690918ce00fe6690918ce00fe6910918ce00bf6688918ce00df6644918ce009fe69c988ce009fe698988ce009fe694988ce009ee690988ce009fe690988ce00dee690988ce009fe688988ce009fe684988ce00bee690988ce009fe2a1978ce009fe690978ce009fe688978ce009f) else (if i < 11 then 0xfeaa993042009fe6a57304200dee6517304200df664d73042009fe6a47304200bee6907304200dee6507304200df664c7304200bfa6887304200bfc6847304200d7e65e3304200dde6563304200dee6523304200df664e33042009faaa99204200dfa69d9204200dfa9dd9204200dfa68d9204200dfa5cd9204200dfa1cd9204200dfa8cd92042009fe6a57204200d7e65d7204200dbe6597204200dde6557204200dee6517204200df664d7204200dfa64972042009fe6a53204200d7e65d3204200dbe6593204200dde6553204200dee6513204200df664d3204200dfa6493204200d7a65e2204200dfa65e2204200dba65a2204200dda6562204200dea6522204200df264e2204200dfa64e2204200d7e65d3104200dbe6593104200dde6553104200dee6513104200df664d3104200dfa6493104200df464e1104200dfc64e1104200df864a11042009fe68c97612009fe68897612009fe68497612009fe69c93612009fe69893612009de69493612009fe68493612009fe69c91612009fe68c91612009ee6909760e009fe6889760e009fe6849760e009fe69c9160e009feaa99720e009fe6a48720e00bf668c8720e009feaa99620e009deaa99520e00ddeaa99520e00dde69d9520e00dde29d9520e00dde21d9520e00dde6999520e00dde6919520e00dde6899520e00dde6859520e00dde2859520e009feaa99520e00bdeaa99520e00dde65d9520e00dde6599520e00ddea665520e00dde65e5520e00dde65a5520e00dee65e4420e00dee65a4420e00dce6564420e00cfe65d8320e00dde9559220e009feaa99120e00dde9559120e00dee9119120e00dde6559120e009fe2a2995ce009fe692995ce00df668e995ce009fe68a995ce009fe686995ce009feaa8985ce009fe690985ce009fe688985ce009fe684985ce00cfe660985ce009fe2a5845ce00deea66445ce00dee262445ce00fce956445ce009fe2a5835ce00cfe261835ce00b7e29d835ce00bde694835ce009fe690915ce00dee910915ce00dfc644915ce008fe2a2991ce009fe2a2991ce009fc286991ce009ee690981ce009fa688981ce009fc684981ce009fe684981ce009eeaa9941ce00dee6a1941ce00dee699941ce00dee695941ce00dee685941ce00cee661941ce00dee661941ce00dce655941ce00dde655841ce00dee651841ce009fe6a5541ce00dee651541ce00dce656441ce00dee656441ce00fce956441ce00dde655831ce00dee651831ce00bf6aa9731ce00dd6655731ce00fe6911731ce00cfe661731ce00dee651731ce009faaa9921ce00dfa6a1921ce00dfa61d921ce00dfa699921ce00dfa695921ce00dfa615921ce00dda955921ce00dfa611921ce00dfa551921ce00dea911921ce00dfa60d921ce00d7a5cd921ce00dfa5cd921ce00dfa68592 else 0x248200bfa28d7248200dfa64d7248200efa60d7248200f7a5cd7248200bfaaa95248200efa2a15248200bfa69d5248200dfa65d5248200fba9995248200bfa28d5248200fda54d5248200bfaaa94248200bfa69d4248200dfa6594248200fba9994248200bfa28d4248200dfa64d4248200fea50d424820097e69c91482009fe69c91482009be69891482009de69491482009fe6949148200dde95491482009ee69091482009fe6909148200dee91091482009f668c91482009fe68c9148200dfa5c89148200dfa5089148200cfe6598148200ebe9998148200efa5c981482009fe6a48148200bfa6888148200d7e65d7148200f7a5c97148200dfc24571482009fe6a47148200bee6907148200bfa6887148200dde6555148200fda5495148200dee6514148200fea5094148200df664d31482009fe6a43148200bde6943148200bfa6883148200bfaaa92148200bfa69d2148200dfa6592148200fba9992148200bfa6952148200fda9552148200bfa6912148200fea9112148200bfa28d2148200efa60d2148200efa6052148200ff84c52148200afe2a21148200ff848611482008ff2a197482008ff6a48748200aef6908748200aff68c8748200afb68887482009fd2859648200bbf6987348200bdf6947348200bef6907348200bfb6887348200efb2a17248200dfb6597248200dfb64d7248200f7b5cd7248200ffa5c93048200cfe2a19344200dde9559344200dee2919344200dee9119344200dfa28993442009fe69c93442009fe69893442009fe6949344200dde9549344200df664c9344200bde6948344200bfc68483442009fe6a573442009fe2a573442009fe6a47344200bee6907344200bfa6887344200bfc68473442009fe6a553442009fe2a553442009fe6a543442009fe2a63344200df664e3344200dde9559244200dee9119244200cfe64d82442009fe6a572442009fe2a572442009fe6a562442009fe6a552442009fe2a552442009fe6a542442009fe6a53244200dfa65e2244200dfa25e2244200dfa65a2244200efa61a2244200fba99a2244200dfa6562244200fda9562244200dfa6522244200fea9122244200dfa64e2244200bfcaa94144200fbc9994144200fec5d14144200fec5914144200dfc64d4144200fec5094144200ff88894144200afe2a13144200df624d3144200bde6943144200dfc64e1144200dfc24e1144200dfc64a1144200efc60a1144200ff888a11442008ff2a193442009ff69c93442008ff6a48344200aff69c8344200aff6988344200adf6948344200afd6848344200bef6907344200bfb68873442009fe6a530442009fe2a53044200df624d3044200bfc2853044200ffa5c920442009f6aa99304200df6aa99304200df669d9304200df629d9304200df66999304200df668993042009)) else (if i < 14 then (if i < 13 then 0xbf668c814c2009fe2a5714c2009fe6a4714c200bee690714c200bf668c714c2009fe2a5514c200afe2a1514c200dde655514c200fd654d514c2009fe2a5414c200bf6aa9314c200ef62a1314c200ef661d314c200fb6999314c200bf6695314c200fd6955314c200bf6691314c200fe6251314c200ef6611314c200fe6911314c200ff2289314c200ef6609314c200ff2889314c200ff4245314c200ff45c5314c200ff4505314c200afe2a1314c200dfc245314c200bde694314c200ff44c5214c2009fe2a6114c200bf628e114c200ff44c6114c2009ef692994c2008ff2a1974c2009fb688974c2009ff688974c200aef690874c200af768c874c200afe680874c2009ff69c914c2009df694914c200aff69c814c200af768c814c2009fe6a5704c2009fe2a5704c200bf628d704c2009feaa9970c200d7e65e770c2009beaa9960c200dbe69d960c200dbe9dd960c200dbe689960c200dbe685960c2009fe6a5760c200dbe659760c200dbe65e660c200dbe659730c200db665a330c200df665a330c200fb699a330c200dbe999920c2009fe6a5720c200d7e65d720c200dbe659720c200dfa649720c2009fe6a5620c200dbe659620c200dfa65e220c200dba65a220c200dfa65a220c200fba99a220c2009feaa9910c200dbe999910c200df68cd910c200dfa889910c2009fe6a5710c200d7e65d710c200dbe659710c200dfc645710c2009fe6a4710c200dbe658710c200bee690710c2009fe6a5610c200dbe659610c200dbe659310c2009fe6a5210c200dbe659210c200dfa649210c200dfc645210c200dbe65a110c200dfc646110c2009fe2a19748200cfe2a19748200dde2959748200afe2a197482009fe69097482009fe68c97482009fe68497482009fe6a48748200bee6908748200bfa6888748200d7e65e77482009fc2859648200dfc2859648200bfc2859648200dbe65e6648200cfe2a19548200dbe9999548200afe2a195482009fe6a57548200dde65e5548200f9e99a5548200dbe99994482009fe6a574482009fe6a56448200dee65e4448200dee25e4448200dee65a4448200fae99a4448200dbe9999348200dde9559348200dee2919348200dee91193482009fe69c93482009be69893482009fe6989348200dbe99893482009fe6949348200dde95493482009fe6849348200cfe65d8348200ebe99983482009fe6a48348200bde6948348200bfa68883482009fe6a573482009fe6a47348200bbe6987348200bde6947348200bee6907348200bfa6887348200bfc68473482009fe6a563482009fe6a553482009fe6a54348200afe2a23348200df664e3348200bfa68a3348200bfaaa97248200dfa2a57248200efa2a17248200f7a9dd7248200dfa6597248200fba9997248200dfa6557248200fda9557248200fea9117 else 0x8748600bef6908748600aff2a277486008ff2a195486008ff2a19448600cff21d9448600aff2a17448600e7f21d7448600eef6117448600aff2a164486008ff2a193486009ff69c93486009df69493486009ff69493486009fe6809348600bdf6948348600aff2a17348600bbf6987348600bdf6947348600bef6907348600bfb6887348600bfe6807348600aff2a16348600aff2a15348600ddf6555348600edf6155348600aff2a23348600fbb5956248600fbb58d62486008ff68c98846008ff68898846008ff2a58384600aff69c8384600adf6948384600afd6848384600cff2617384600cff2607384600bfb6887384600cff26233846008ff2a192846008ff2a58284600cff2617284600dfb6497284600cff2615284600cff2614284600cff2613284600cfb26222846008ff2a190846009fe6a47350200bbe6987350200bde6947350200bee6907350200bfa6887350200bfc6847350200afe2a23350200fba99a22502009fe6a47150200bee6907150200beeaa94150200fae9994150200fea8894150200fec50531502009fe6a43150200bde6943150200bee6903150200bee692994c2009fe698984c200cfe2a1974c200dee291974c2009fe690974c2009fa688974c2009fe688974c2009fe684974c200d7e65c974c200bfa688974c200afe2a5874c200bee690874c200bf668c874c2009fe2a6774c200afe2a2774c200dbe262664c200ebe61e664c200cfe2a1954c200dbe999954c200f9e99a554c200dbe999944c200deea64944c200dee65c944c200dee25c944c200dee658944c200fae998944c200ebe999844c2009fe6a5744c2009fe2a5744c200eee611744c2009fe2a5644c2009ee2a6444c200bee2a6444c200dee65e444c200dee25e444c200fae99a444c200bde694834c200afe2a1734c200d7e25d734c200bbe698734c200bde694734c200bee690734c200bfa688734c200bfc684734c200afe2a1634c200bf6aa9534c200ef62a1534c200df665d534c200fb6999534c200fd65d5534c200afe2a1534c200bf6aa9434c200fb6999434c200fe65d1434c200fb699a334c200df6652334c200fe6252334c200ef6612334c200fe6912334c200bf6686334c200dee251924c200ebe999824c200ef68cd824c2009fe2a5724c200bf628d724c2009fe2a5524c200fd654d524c200eee611424c200fe650d424c200dfa65e224c200dfa25e224c200efa61e224c200fba99a224c200dfa656224c200fda956224c200dfa652224c200fea252224c200efa612224c200fea912224c200ff254e224c200ff250e224c200ff28ce224c200dee251914c2009fe69c914c2009de694914c2009fe694914c200dde954914c2009fe690914c200dee910914c200df68cc914c200bde694914c200dee250914c200dfc644914c200) else (if i < 15 then 0xcff262774c6008ff2a5864c600cff261764c600cbf262664c6008ff2a1954c6008ff2a5854c600cff261754c600cff261654c600cdf262554c6008ff2a1944c6008ff2a5844c6009ff2a5744c600cff261744c600eef611744c600bf728d744c6009ff2a5644c600aff2a1644c600cff261644c600cef262444c600cf7a64834c600ef79dc834c600af7698834c600ef75d8834c600eb7998834c600cf7654834c600ef75d4834c600ef7594834c600ed7954834c600bf6680834c600bdf694834c6009ff2a5734c600aff2a1734c600cff261734c600bbf698734c600bdf694734c600bef690734c600bfb688734c600bfe680734c600af72a1634c600ef72a1634c600fb75d9634c600fb7591634c600ff5285634c600aff2a1634c600cff261634c600bfd285634c600aff2a1534c600cff261534c600edf615534c600cff261434c600cfb260924c600dfb25c924c6008ff2a5824c6009ff2a5724c600cff261724c600cff261624c600fb758d624c6009ff2a5524c600aff2a1524c600cff261524c600cff261424c600bf7699324c600ff35c9324c600ff3509324c6009fb2a6224c600cfb262224c6009fd2a5714c600ef520d714c600cfd261414c600fed5d1414c600dfa249904c600bbe698904c6008ff2a2990c6009ff69c980c6009df694980c6009ffaa9970c6008ff2a1970c6009ff68d970c600cff661970c6009ef690970c6009fb688970c6009fe680970c6008ff6a4870c600c7f65c870c600aef690870c6009ff6a5760c600d7f65d760c600dbf659760c6009dfaa9950c600cdf6a1950c600cdf2a1950c600ddf69d950c600cdf61d950c600cdf21d950c600ddf9dd950c600ddf699950c600cdf619950c600ddf5d9950c600d9f999950c600ddf691950c600ddf689950c600dde681950c600dde281950c6008ff2a1950c600cdf661950c600ddf65d950c600cff65d850c600cdf655850c6009ff6a5750c600ddf655750c6009ff6a5650c600ddf655650c600cff65d840c600cdf655840c600d7f65d740c600ddf655740c600eef611740c600dbf659640c600ddf655640c600dcf656440c600cff65d830c600cdf655830c600ddf655730c600ddf655630c600ddf655530c600cff65d820c600cdf655820c6009ff6a5720c600d7f65d720c600ddf655720c600dfb649720c6009ff6a5520c600ddf655520c600ddb656220c600cff65d810c600cdf655810c600ddf655710c600ddf655310c600cfe61d900c600cfe619900c600dbe999900c600dde955900c600cfe611900c600dee911900c600cfe609900c600dfa889900c600df64c5900c600dde655900c6008ff2a299486008ff2a197486009ff68c97486009fe68097486008ff6a48748600cffa648748600aef6908748600aff6908748600aff68c8748600aff680 else (if i < 16 then 0xd424ca00dfb659424ca00eeb611424ca009ff69c914ca009df694914ca00dfb5c8914ca009fe680914ca00aeb6908788a00afb6908788a00afb68c8788a00afb6848788a00afb6808788a00beb6908788a00bfa6808788a00afb2a27788a00edb6156588a00ebb9998488a00afb2a17488a00e7b21d7488a00eeb6117488a00afb2a16488a00eeb21e4488a00fab99a4488a008fb2a58388a00ebb9998388a00bdb6948388a00bfa6808388a00afb2a17388a00bbb6987388a00bdb6947388a00beb6907388a00bf96847388a00bfa6807388a00afb2a16388a00afb2a15388a00edb6155388a00afb2a23388a00affaa973606008ff2a57360600aef6907360600afb6887360600aff6887360600afd6847360600afe6807360600affaa972606008ff2a57260600e7f5cd7260600efb5c96260600afd2856260600affaa93260600aff69d3260600aff6993260600efb5c93260600ebb99a22606008ffaa99320600cdf9559320600cef9119320600affaa973206008ff6a57320600cff65173206008ff6a47320600aef6907320600aff6907320600cff6507320600afb6887320600afd6847320600afe6807320600affaa953206008ff6a55320600cdf6555320600ef75cd5320600affaa943206008ff6a54320600aff69d4320600cff65d4320600eef5d14320600cff6563320600cff6523320600cf764e3320600cff5cd9020600cff1cd9020600aff69c8320600adf6948320600cf764c8320600afd6848320600bef6907320600bfb6887320600cff21d9220600dfa88990206008ff69c98506008ff69898506008ff68c98506008ff68898506009ff68c97506009ff68897506009fe68097506008ff6a48750600aef6908750600aff68c8750600aff6888750600cff2627750600cff2617650600cbf26266506009ef2a57450600aef2a17450600e6f21d7450600bef28d7450600aef2a16450600bef28d64506009ff69c93506009ff69893506009df69493506009fe6809350600cff2617350600f6f5d17350600cff2607350600bbf6987350600bdf6947350600bfb6887350600cff2616350600faf5916350600cff2623350600cff2617250600cff2616250600eef21d4250600bef28d4250600feb5894250600cff2613250600feb5093250600cfb2622250600efd9dc8150600eed5d08150600afd68c8150600efd5cc8150600efd1cc8150600efd8cc81506008ff2a2994c6009ff69e994c6009ff696994c6009fb68a994c6008ffaa8984c6008ff69c984c6008ff698984c6008ff694984c6008ff690984c6008ff688984c6008ff2a1974c6009ef690974c6009ff688974c6009fe680974c600bef690974c6008ff2a5874c6008ff6a4874c600aef690874c600afd684874c600aff680874c600bef690874c600aff2a2774c60 else 0xefb6a17258a00efb2a17258a00dfb2617258a00efb61d7258a00efb6157258a00efb6117258a00bfb28d7258a00efb60d7258a00f7b5cd7258a00fbb58d7258a009ef6909158a009f768c9158a009ff68c9158a00dfb5c89158a009fe6809158a008ff2a29954a00cff2a29954a009ff69e9954a009ff69a9954a009ff68e9954a00aff2a29954a008ffaa89854a008ff69c9854a00cff69c9854a008ff6989854a00cff6989854a008ff68c9854a008ff6849854a00aff69c9854a00aff6989854a00aff6849854a00edf5449854a009ffaa99754a008ff2a19754a00cff2a19754a009ff6999754a00aff2a19754a00cff2619754a009ff68c9754a009fe6809754a00aff2a27754a00cff2627754a00aff2a19654a00cff2619654a009ff69c9354a009ff6989354a009fe6809354a009ff2a57354a00aff2a17354a00cff2617354a009ff6a47354a00bbf6987354a00bdf6947354a00bef6907354a00bfb6887354a00bfd6847354a00bfe6807354a009ff2a56354a00aff2a16354a00cff2616354a00ddf65d5354a00fd75cd5354a009ff2a63354a00aff2a23354a00afb2a17254a00efb2a17254a00cfb2617254a00efb2617254a00f7b5cd7254a00fdb54d7254a00aff2a19154a00cff2619154a009ff69c9154a009ff68c9154a00dfb5c89154a009fe6809154a008ff2a29950a008ff2a19750a009f728d9750a009fe6809750a008ff6a48750a00cffa648750a00aef6908750a00aff6848750a00aff2a27750a008ff2a19650a00cefa658450a00cef65d8450a00eef9dd8450a0097f69c9350a009ff69c9350a009bf6989350a009ff6989350a009df6949350a00cef6109350a009fd6849350a009fe6809350a00aff2a17350a00d7f65d7350a00eef6117350a00aff2a16350a00dbf6596350a00eef6116350a00df724d6350a00dfb65d6250a00eeb6116250a00dfb24d6250a00fbb58d6250a00feb50d6250a009ff69c9150a009fe6809150a008ff2a2994ca009ff69c984ca009ff698984ca009ffaa9974ca008ff2a1974ca009fe680974ca00cffa65874ca008ff6a4874ca00aef690874ca00afb688874ca00aff684874ca009ff6a4874ca00bef690874ca00bfb688874ca009ffaa9964ca008ff2a1964ca00cff2a1964ca00cff61d964ca00aff2a1964ca00cffa65864ca00cff65d864ca009ff6a5764ca009ffaa9954ca008ff2a1954ca00ddf545954ca00cffa65854ca00cff65d854ca00cff659854ca009ff6a5754ca009ff6a5654ca00edf615654ca00cff65d844ca00cff659844ca00eef611744ca00aff2a1644ca00aff2a1634ca00edf615534ca009fb2a5724ca00dfb2a5724ca00dfb261724ca00dfb659724ca00efb619724ca00dfb655724ca00efb615724ca00efb611724ca00f7b5cd724ca00bfb69))))) else (if i < 26 then (if i < 21 then (if i < 19 then (if i < 18 then 0x157354e00aff2a17354e00edf6157354e00bbf6987354e00bdf6947354e00bef6907354e00bfb6887354e00bfd6847354e00bfe6807354e00edf6159254e00aff2a19154e00cff2619154e00edf6159154e00ef720d9154e009ff69c9154e009fe6809154e00edf6149154e008ff2a29950e008ff2a19750e009fe6809750e008ff6a48750e00aef6908750e00aff6848750e009ef2a57450e00e6f21d7450e00f6f5d17350e009ff69c9150e009fe6809150e008ff698988ce008ef690988ce008ff690988ce00cef690988ce008ff688988ce008ff2a5848ce00cef651848ce00eef5d1848ce00cef262448ce008ff2a1928ce008ff2a1918ce009ff69c918ce009ef690918ce009fe680918ce00bef690918ce008ff2a1908ce00bfa688908ce008ff2a67760a00affaa97360a008ff2a57360a00abf6987360a00aff6987360a00adf6947360a00aef6907360a00afb6887360a00afd6847360a00afe6807360a008ff2a63360a008ff2a2995ca009ff69a995ca009ff696995ca009ff68e995ca008ffaa8985ca00c7f9dc985ca008ff698985ca00cff698985ca008ff694985ca008ef690985ca008ff690985ca00cef690985ca008ff68c985ca008ff684985ca009ff698985ca009ef690985ca009ff68c985ca00aff698985ca00aff694985ca00aef690985ca00aff690985ca00aff684985ca00bef690985ca00bef690875ca00aff2a1965ca00cff261965ca008ff2a5865ca00cffa65865ca00aff2a1955ca00cff261955ca008ff2a5855ca00cffa65855ca00cff261755ca00cdf262555ca00aff2a1945ca00cff261945ca00bf728d945ca008ff2a5845ca00cffa65845ca00eef651845ca00aff2a1745ca00cff261745ca00eef611745ca00cef262445ca009bf698935ca009ff698935ca009df694935ca009ff694935ca009ef690935ca009fd684935ca009fe680935ca00bbf698935ca00bdf694935ca00bef690935ca00bfd684935ca00bfe680935ca008ff2a5835ca009ff6a4835ca00b7f69c835ca00bdf694835ca00bfb688835ca00e7f619735ca00e7f615735ca00e7f611735ca00bbf698735ca00bdf694735ca00bef690735ca00bfd684735ca00bfe680735ca009ff2a5635ca00aff2a1635ca00f775cd635ca009ff2a5535ca00edf615535ca00f775cd535ca00aff2a1915ca00cff261915ca009ef690915ca009ff68c915ca009fe680915ca00bef690915ca008ff2a29958a009ff68c9858a009fe6809858a00aff2a19458a00cffa658458a00aff2a19358a009ff69c9358a009ff6949358a009fe6809358a00cffa658358a009ff6a48358a00bbf6988358a00bdf6948358a00aff2a17358a009ff6a47358a00bef6907358a00bfb6887358a00bfd6847358a00bfe6807358a00aff2a15358a00edf6155358a else 0x500020800f0006e003200118007800320014000780028000a0000cff5959720e008ffaa99620e00cff5d59620e00cff5c19620e00cdfaa99520e00cdf69d9520e00cdf29d9520e00cdf6999520e00cdf6859520e00cdf2859520e00cdf6819520e008ffaa99520e00cff6999520e00cdf65e5520e00cdf65a5520e00cdf9559120e009ffaa99720e00aff6988720e00af768c8720e009ffaa99620e009dfaa99520e00ddf69d9520e00cdf21d9520e00ddf6999520e00ddf6899520e00dde6819520e00ddf65d9520e00ddf6599520e009ff696995ce009ff68a995ce00cff698985ce00cff5d8985ce00cff5d4985ce008ff690985ce00cff58c985ce008ff688985ce008ff684985ce009ff688985ce00aff698985ce00cff658985ce00aff694985ce00cff654985ce00ef758c985ce00aff684985ce008ff2a5845ce00cffa65845ce00cef262445ce00bdf694835ce00aff2a1915ce00cff261915ce009fe680915ce008ff2a2991ce009fd286991ce009ef690981ce009fb688981ce009fd684981ce009efaa9941ce00cef6a1941ce00dee681941ce00cef661941ce00dcf655941ce00cdf655841ce00cef651841ce00dcf656441ce00cdf655831ce00cef651831ce00dd7655731ce00def651731ce009fbaa9921ce00cfb6a1921ce00cfb61d921ce00dfb699921ce00dfb695921ce00cfb615921ce00ddb955921ce00cfb611921ce00deb911921ce00cfb60d921ce00d7b5cd921ce00dfb5cd921ce00dfb685921ce00dfa681921ce00dfb681921ce00cff61d921ce00cff615921ce00cfb661921ce00dbb659921ce00ddb655921ce00deb651921ce009fdaa9911ce00cfd6a1911ce00cfd2a1911ce00cfd611911ce00ded911911ce00cfd60d911ce00dfd5cd911ce00dfc681911ce00dfc281911ce008ff2a1911ce00cfd661911ce00ded651911ce00df9649911ce00def651911ce00dfb649911ce00cfe611901ce00dee911901ce00cfe60d901ce00dfe5cd901ce00cfe661901ce00dee651901ce00dfa649901ce00dfc645901ce00dfe645901ce009ff69e9954e009ff69a9954e009ff68a9954e008ffaa89854e008ff69c9854e008ff6989854e00cff6989854e00cdf6949854e00cf78cc9854e008ff6889854e008ff6849854e00aff6989854e00aff6849854e00edf5449854e00aff2a19754e009bf6989754e009ef6909754e009fb6889754e009ff6889754e009fd6849754e009fe6809754e00bbf6989754e00bef6909754e00bfb6889754e00bfd6849754e00bfe6809754e00aff2a19654e00cff2619654e00b7f29d9654e00cdfa658554e00edfa658554e00edf65d8554e00cdf25d8554e00edf25d8554e00edf6598554e00cf7a648354e00af769c8354e00ef76588354e00af72a17354e00ef72a17354e00ed76) else (if i < 20 then 0x64f0326e19280c69862e8316a18a60c50862483106186a0c2d86130307a181a0c0586018300217fc0bfb85fa02f9e17c00bd885e882f2617840bbf85dc02ec217520b9c85ca82e36170c0b8385be02dd2169e0b4785a002ce216620b06856e02b52159a0ac5855f02aee15720ab1855282a62152c0a898541029ea14e60a6b852f8294a14960a3e851b828be14500a2085050280a13f609f384f38279213c409da84e98272e139209bc84da826a21342099484c90262a1310098084bf025da12e8097184b78259e12c0095384a6024fe1270092b84920245e122009038480823fa11f808f984718238211b208cc8462822f6116c08b38458822ba1130089584470222e11120881843d021b610cc08598429021161086084084128208a10360813840381ffe0ff007f583f981fc20fdc07eb83f481f9a0fc807d783e801f0e0f7807b483d401e820f32079183c501e0a0ef6077383b881dba0ed8076483b101d7e0eb0075083a701d2e0e7e073c839d01cca0e60072d839301c7a0e380719838b81c160dfc06f6837a01bc60dd406e7837281b8a0dc006dd836d81b4e0d9806c9836381b120d8406ba835981a5e0d200683833e019d20cd0065b832a019320c8a063d831b018a60c3a06158307018060bf405f782fa817ca0bd605e882f30178e0bc205de82ee017660bae05d482e4017020b6805ac82d0016620b18058482c1015fe0ae6056b82b2015720aa0054882a0814e60a64052582828140a0a0004fd827d813e209e204ee8276013a609ba04da826c01356099c04cb82648131a098804ad824b81252091a048a823f011ee08f2047182378116208ac0453822881126088e04308217010ae0852042682120107208340417820a8104a0820040d82058100e080203fe81fe00fe607ee03ef81f680faa07d003e581f180f82079e03c781e280f0a078003b881db00ece075803a981d100e7e0730039581c980e42071c037781ba80db606cc036381b080d7a06b8035981ab80d5206a4034f81a680d2a06900340819f00cda065e032c818b00c4e0622030e817c00bd605e602f0816d00b5e05aa02d2816800ae6056e02b4815900abe054602a0814f00a6e050a0282813d809ce04d80264812e8096a04b0025581270091a0488023c810e00852041a020a80ff007da03de01e780f00077603ac01ce80e3806fe037001b080d7006ae034801a180cf806720334019780ca806360316018380be005d202da016a80b40059602c6015b80ac80532028a01388098804920244011a808c004560226011080870042e02120106807f803f201f400f28078003b601d600e380708037a01b800d980690032a019000c0805f002da016800b18057802b20140009d804d8024e01180084803e801d600e6006b80348018600b40057802800122008c00438020800aa else 0x35e19ac8cd28668a3340199d8ccd8664e3322198e8cc606626330e19848cbe865ea32c8195c8caa86536329619348c99064be325a192a8c9406496324619208c8f0646e323219168c8a06446321419078c82863f631f618f88c7b063ce31d818e48c6e8636a31b018c18c5f862f2314c188f8c4406216310618808c3f061ee30f218628c300616230ac18538c288613a309818498c21060fe3048181c8c030600e2fee17e08bef05f322f6c17b38bce85e6a2f3017958bc985df22eea17728bb585da22ec2175e8bab85d522e7c173b8b9c85cc62e5417228b9005c762e2c17138b8885c3a2e1817098b8105bfe2df016f58b7985b722db416d78b6085afa2d7816b98b5185a822d3c169b8b4c85a5a2d2816918b4785a322d0a167d8b338597e2cb016508b22059062c7e16378b18058a22c4c16238b108587a2c2e16148b06858162bfc15f68af78579e2bc015d88ae3856d62b5c15a68acf8564a2b0c15798abb855d22ada156a8ab4055962ac6155b8aac8555a2aa815518aa2854e22a6215248a8e854422a1214fc8a7a853ca29e014ed8a75853a229cc14e38a7085366299a14c58a5f052ee296814ac8a5285262292214848a3e851d628dc146b8a320515e28aa14528a2805122288c14438a20850d22846141b8a0a05046281e140c8a0504fa627ce13df89ee84f56279c13c689df84eca276013ad89d584e8e272e138f89c404dee26f2137189b504d8a26b61344899e84cc226521326898f84c5e26161303897b84bbe25d012e0896a04b32258012b8895384a6a251c128b894484a1a25081281893f849f224f412778938049b624c21254892684902247212318917848b2244a121889088481223fa11f088f48477223aa11cd88e0846fa237811b488d9046be235a11aa88d18466e2332119688ca04646231e118788c0045e222ec116e88b60459222ba115588a70451a2288113288958448e2242111488868440221f210f188750438a21c010d8886884326217a10a1884d0424a212010888840841d220d0105b88250411e208a103d881b040ba204e102488110406a2026100b880203ff21fea0fed87f583fa21fc20fd987e903f2a1f860fbb87da03eb21f4a0f9387c103dd61ed20f6187aa83d4a1ea00f43879b83cbe1e500f20878c83c321e140f07878283c0a1e000ef8877b03bba1dce0ee4876e83b6a1da60ec6875f83af21d740ead875083a521d100e7b873c839da1cde0e678730039621ca20e498721038fe1c7a0e3a871c038ae1c480e21870d0384a1c160e0386fe037d21bda0de586ec837321b940dc286e0036e21b6c0dae86d6036921b300d9586c2035f21ad60d5e86a9035161a720d2c86950349e1a400d1386860341219fa0cf086720337219b40cd286680332219820cbe865e032e6196e0cb48659032be19500ca58)) else (if i < 23 then (if i < 22 then 0x1e0a0d25064282a94140a09650462820940f0a06e50322816940a0a03250142807940009ff64ff627f893fb09fce4fe227e493f109f7e4fb027d593e989f2e4f8827bc93d589e8e4f38279493c689e164efc277693b789d8a4ec0275893ab09d3a4e982744939e89cd64e5c272b939489c9a4e3e271c938a89c4a4e162703937e09bbe4dd026e5937189b824db226d6936789b324d9426b3935889aa64d4e26a4935109a7e4d3a269a934c09a424d1c268b9338099b64ca4264f931a098c64c4a260992f70975e4baa25cd92e5897224b7825b992d9096aa4b4625a092cc8965a4b28259192c78961e4b00257d92bb095ba4ace255f92ae895064a74253292958948e4a38251492890942a49fc24f6927789362499824c4925c092ae493e249292430920e4902247e923b891d248d02460922a09132488a243d921b090ba484e2424920e890564812240191fd08fb647cc23de91e908f2a479023c091df08eda476823b191d508e8a4736239391c888e3a4718238491be88dea46e6237091b708d8646962343919688c96461e22f8916e88b42459222c1915d08aca456022a8914e08a3e4506227b9137889b244d42262912d8896244ac224e9123888fe44702230910f8885e440c21fe90fb887be43d021e590ef0875a438021b890d60867e4330219590c70861a42f4217790ba885ca42d6216390ae0855242902140909c884c64254211d908b08426420e2104907e883d641dc20e6906d08336418c20af90540824640f6206e90310816a40a6204b9022080f2406a202d90130807a4024200a900187fee3fe81fec8ff287f8a3fb61fd38fe387f123f841fba8fdc07ec23f521fa68fd207e723f2a1f8d8fc087dfa3eee1f6a8fb187d6e3ea81f478fa007cce3e581f248f9107c7e3e261f0b8f8487c063df41ef78f7a87bca3dd61ee38f7087b7a3dae1ecf8f6687b163d7c1eb68f5787a9e3d401e988f4887a123cfa1e708f370799a3cbe1e578f28079223c821e2a8f118786e3c281e078f028780a3bf61df88ef8877a63bce1ddf8ee98772e3b921dc68ee2077063b7e1db78ed8076b63b421d998ec1875da3ac01d498ea1074ae3a481d0d8e80873d239b21ccc8e60072ce39581c9f8e4c0724239081c778e38071b638d61c638e2e0716638ae1c4f8e21870ee38681c2c8e128707638221c048dfc06fc237c81bdc8dea86f36378c1bbe8ddb86ebe37501ba08dcc86e4637141b828dbd86dba36d81b648dae86d56369c1b468d9f86cca36601b2d8d9586ca2364c1b1e8d8b86c3e361a1b0a8d8406c1636061b008d7f06bee35f21ace8d6386b12357a1ab58d5486a72352a1a8d8d45869e634e41a658d2c86946348a1a388d1886842341219fc8cf8067a233cc19e38cf08675233a419cf8ce68672a339019c58ce1866ee337219b68cda066c63 else 0xa43ccf9e640f302797c3cbb9e5c8f29e79363c939e460f226790e3c7f9e3c0f1c278dc3c669e258f10e78783c349e190f096783c3c169e050f00a77ec3be49dee8ef56779c3bc69ddd0eeca77423b949dc68ee1676fc3b719db78ed9e76c03b589da60ed1276703b309d948ec5e76163b039d7b8ebd275da3ae09d6a0eb3275763aa99d538ea6a751c3a869d3a8e9a274b83a409d1c8e876740439fa9cf70e74a739639be9cd18e65a731e39879cbd8e5e272e239699cae8e5427292393c9c9a8e4b6724239149c868e40271e838e79c700e362719838c99c5e8e2c27152389c9c4a8e2227102386f9c318e15a709438429c1d8e02e6fc237bb9bd50de126ebe37529ba30dce66e5a37259b8c8dc326e0036ee9b738db6a6d9c36c69b5d0daca6d5636a39b508da7a6d2e368a9b378d99e6cc036589b288d9126c66362b9b0f8d85e6c1636089b030d7e66bd035e09aec8d7466b9435c29adb0d6a66b4e35a49ad10d67e6b3a359a9acc0d6566b1c358b9ac20d5de6ae035639aab8d53e6a9035459a9f0d4c66a5e352c9a950d49e6a2235049a6f8d34a698234969a3d8d1ba68c434509a248d11a688834329a0e0d052681a340099fc8cfc667d433e299ed8cf3a677a33b599d48ce72672a338d99c30cdfa66ee336f99aa0cd32668a333d999b0cca66644331a99870cc1a65fe32f799780cb8e65b832d499668cb16657c32b199528ca26650e326b99280c8d26432321699050c7f663e231e498ec0c72e635631a898c18c5ee62e8316c98b28c576628e313f98998c49a6220310898808c3d261da30e5986f0c35a619430c2985d8c2a66144309a98498c22e6108307c983a8c1b660cc305e982e0c16660ae305498290c0ee6072303698178c0b260543022980d8c04e6022300998010bfea5fe62feb97f20bf865fb42fd797ea8bf4a5f962fc897e30befa5f6e2fb497d90be1e5ef62f5097930bbee5da22ec997598baae5d482e9c974a8b9aa5cc62e3d971b0b8a65c442e1596ff8b7f25bd62dde96e90b73e5b722db696d78b69e5b222d8496bc0b5c25ad22d6196a58b50e5a782d25968c8b40a59f62cf396788b31a597e2c99963a0b13a58842c3a96198b0ae58482c1c960a8affa57e42bea95f18af6e579e2bcc95e28ae6a57262b6d95a40ad0256722b3195950ac8a56362b1895888ac2655fa2af595770ab9a55be2ad795680aae655462a9b95428a9f654c42a5a952c0a94254922a41951d0a8ca544c2a1e95090a82a53e829f194f78a78a53a229ce94e10a6ea537029a194cd0a65e5320298894c08a5fa52f8297494b90a59652bc295194a50a51e5280293894988a4a65244291a94898a44252122901947d0a3ca51d628e3946e0a352519028c0945c8a2da516828b194460a2125104287a94370a19a50c8285c94280a1225082283e94) else (if i < 24 then 0x7967e2b3d859dfacec16706b338597bacb296526b2705926ac8a96396b1b258ccac5d962a6b13a5890ac42161cab0ae584aac1c9609eb02c57faabf215f5eaf7857b4abd695e0aaeba5755aba215cdeae1056fbab7795afead525679ab2515856abcc55caaada1563aaafa5575aab495536aa3c54daaa581523ea8f25467aa2d950fea866542baa0a94fe6a7da53d6a9e794ee2a73a5386a9ba94d8ea6ae534aa99a14c8aa6365313a98614baea5be52d7a96094afaa57852b4a95414a46a5005269a92e9491aa4605219a901947b2a3ac51c9a8de946c2a3485188a8bb945bea2a85142a89b14492a1f450e3a85f14262a1045070a82f9410ea064501ba80293fe29fce4fd5a7e713f1a9f384f80a7ad93d3a9e844f35a78f93c4a9e0c4ef9a76513af69d624e9aa742139ca9c7c4e1da6f99379a9bb44dcda6e31365a9ad84d5aa69a9342a99fc4ce7a661132d6995c4c97a643131fa98e44c38a6139306a98084bd4a5e192eb2972c4b7aa5b712d22966e4b25a58c92c1e95ec4aeea56e92ade95564a99a541929c694984a3aa5149285e940c49f4a4ef1275a939449bda4d61266a9326498ba4c49261a92fe497ca4ba925ca92e04968a4a6924da92544922a4799239a913c4887a43d921a690b0484ba41a9207a901a47fba3fc91fc68fca47cea3dc11e228eda4765a3aa11d1e8e6c4724a38991bf28dd646d9a36411ac68d4a4698a343919d68c824616a2fd917ba8b7e45b7a2d5916668b244585a2b2915268a7a4535a2949144a8a0c44fea2741138289b244d1a262912f6896c44aea2561129289304495a2471121a88fe4477a2381118e88ae444fa224110ee88684418a20891026880e43ffa1fc10fae87be43d7a1e810f36879643c3a1de10ed2876443aaa1cf10e5a871e438ca1c290de286d84369a1ae90d42869c4346a1a210d06866a432da19590c7a86244305a17c90bb285ca42e2a16d90b3a858e42bfa15c10ad6855c42a1a14d10a5e852a428da14590a228502427ea13e109be84bc4256a1279091e8476422ea11390892843a4215a1071082e84124201a0ff907de83e041e8a0ee10752837241b1a0d290676832c4193a0c6105fe82fa4170a0b49057282aa4148a09b904aa823c4116a0829040a81f640f3a0761037e81b040cba05f902de816040a3a04e102528124408aa041901ee80f2406ca0329017680ac404ea0211005e7fda3fd69fd38fe1a7ed63f599fa40fcc67e363f099f7e8fbea7de63ef09f6d0fb4a7d963ec39f5e0fad27d503ea59f4f0fa0a7d003e789f3b0f9ba7cc43e5a9f270f91a7c743e379f0e0f8667c243e0a9f040f8167c063df69ef50f7767ba23dc99ee10f6ea7b663da69ecd0f64a7b163d7e9eb90f5aa7ad03d609eac8f5467a943d429e9d8f4ce7a4e3d1f9e898f42e79e03ce89e708f36679 else (if i < 25 then 0xc8563c295213c3096e84afc245211a7086a842dc20420fef07e883ecc1e3a0e7306c68329c18c20c1b05ae82cfc152a0a6304dc8234c0fb206f3034c8199c0c6a05ef02a28112c067a03330158809fc030a012b007c8031c012a0062ffb47faabfbd9fd92fe747f14bf841fbeefdde7ee2bf689fb12fd7a7eb0bf549fa5efd207e6fbf2f1f95afc9e7e29bf139f806fbf47ddebee69f702fb547d93bebe9f59afaa07d39be969f482fa1e7d02be7d9f3a6f9c47cd5be5a9f22af9067c4ebe059effaf7947baebdce9ee2ef7087b4abd7e9ea82f5147a50bd091e816f3de79e2bce11e6aef3347983bcbe1e5bef2947942bc7d1e3b6f1547884bc349e10ef03c77f8bbe99de8eeee87744bb999dc9aee2a76eabb719da92ed447659bb0d9d74aeb6e7587bab89d592eab0754bba9f9d4b6e9fc74e7ba6d9d326e97074abba549d182e8a87447ba201cff2e7e073deb9eb9cf16e76873a2b9b21cd4ae6967339b9919cc5ae61472d5b95f9ca16e4ca722bb8fe1c76ee39471b3b8ce9c61ae2ea7122b8889c412e1e670e6b86a9c322e17870aab84c9c21ee0ec7064b8221c0dee0567005b7fc9bfc6dfca6fd8b7e11beaedf486f92b7b19bd5ade946f3db7989bc92de306f06b77f9bbb6ddc26ed9b7669bb02dd686ea7b74b1ba26dcfa6e6bb7321b94adc8c6e43b7191b896dc326e02b6fb1b7a6dbc46dcbb6d59b63edb066d58b6949b49ada346d0db6809b3bed98a6c81b63f9b0eed8726c09b5f99af9ad7b46bcdb5e09aed2d70a6b7db5b89ad92d6ba6b50b5a21accad6426b14b5891abeed5d46ae2b5689ab26d57a6aabb54d1aa0ed4e46a5bb5251a8e2d44e6a1fb5099a7f2d3e069e3b4eb9a6dad3546989b4c11a5fed2e66966b4af9a536d26e692ab4919a3ced1746871b4351a072d01667b3b3cc19e2eceae674fb39c99cb2cdd266c8b34a199f6cc886628b2fc99726cb7a65b0b2d21965ecb206583b2b919596ca766529b28e9941ac9ea64edb25f192c6c94a6498b23499186c8a06425b1f618f1ac76a63a8b1ce18e52c7106353b1a898d12c670632bb18f98c4ac60c62d1b16018acec5446295b144989dec4e0625eb12698902c4686227b1101879ac3aa61d2b0e5986e6c36461a5b0cc98646c30a6178b0ac1851ac2606123b08e18402c1f260f1b07518376c1ac60ceb063982eac17060abb0521825ec1206088b043181bec0da6065b02f1815ac09e6047b020180e2c0626029b00e98042c0125ffcafe697e9ebf045f6bafa097cbebe465ef3af7397b6abd745eadaf5097a3ebd065e80af2d9793abc845e35af00977bebb805d9faec4975cabaae5d40ae901744eb9c85cafae541726eb8ce5c5aae24970f2b8565c19ae0697002b7de5be2ade116e86b7165b83adbe16dbeb6da5b42ad8c16bb6b57c5aacad4d96a4eb4be5a20ad0 else 0x8800014343884291c3238647090e23888711c44384023840b1844d080000000058c202002020023b8e6350aa26897c380c81dc0310055080060896113403130e161c226846311e021c04100000018225806294032806500f0e1e1c200183c3844b089a0189870b0e11342000420104651544d12c4200a8038041808200860208e6350ca2a89a258840120731a8651544d12c420090028405080a15642002041408421204210810108428082c004050c0413660213c6c008050c04210a020c04160030104681960210890106020c0411080110002c85800804100854009020a042109020a04210802c8412c8412c840005001408281084240828108424082810842408281084240828108420000015c5540842201590d8f4009020a0414082000055135021088056420050014082810842408281084240828108420006815c4d40842281590d001b8c02100410082000000000163804200423180c20182030406000401840108061c1c38384030e8e10000b1840000c200840018c031000b1840000c200840000c625806300c201840058c20000000006100420000183864708d02a897a3e0e5c1c22cc8e200c3a3844700c431806200c24007070e0e1c1c283884211c031006100c225e0e200c200016308000000000006381c531846381c531846381c531846381c531840012c03148e191c323844b00c52384060e0e191c28388e21a065268912000030000000800800022e0010000200200000719b26818e42689120000200420818751c4003c6103c6ecba0e3900003c61070fa3d8ee390000000e384000000000841000000100100000000c710880198e1000071840031c203642031c2000006818e21100401a013402000000000000000680406385e3082c7a1e4731c80002c7a1e4731c80002c7a1e4731c80000163d0f2398e4000001a0c710000b1e8791cc720004080810102008480080000043280410107fb1544d12c06808d0106020804700850104c7090010142040824007020e0414082810400564200000003c61020415402718401080000100100d481090208d481090208a08108023840000000000800800638400008410000010822104028040210400000e331c40058e1b1c26386c7098e1058e100841b1c2031c221040000d032884011006c840001c610000000011b2a8d51c6a0234bb19ea8cbbc63c230bf17e28bcbc5d322d8b16c08b58c5a8a2d27167a8b30c585a2bfb15ee8ae5c56022aa715308a8bc53d229b714c28a4fc526a2903145e89f5c4f4a26ab13288987c4bda25e312ce8964c4aea2543122e8905c47f223b311c088d3c4662229b11208883c43ba21ab10c6882ec413a1ff30f86878ec3ad21d4b0e5a8707c382a1be30de286cbc35321a7b0d1a8658c328a18730c2a85efc2f6a17830b9e85c7c2dda16930b1)))) else (if i < 30 then (if i < 28 then (if i < 27 then 0xe4c1c22cca123c0041418010a1838b5012f47c1c06288e01884bc1c425e0e2c1c225e0e2c1c383844bc1c58388e291c20028e151c20048e118e0714a0181c32805800c0e181c4710af038a0711c528044720840106470804191c20087470e8e1d1c20187070802100c3a387470896a38818384010e0e1c1c200870708d583880000018387070e0e1000000000000ee398d42a89a25c8f03a2070824708d411aa0710d503887308aa100970388e312c225c0e21420714a011418010a103880208ca2b89ba388401180208b32388478084680400068f0008000000003c610000000080080000100100000000e3080e33644720086c84e309c61068f83c8ea3900000000000000000038c2001c610000034026c84d00801a3e0f23a8e400347c1e4751c84d122400004200200000000ae26e8f001006c840000000134202689113480000b23845713747c1c8038e4710ae26e8f839004d1b3238c5713747c1c8015c4dd1f072000001c62688e40104d0804d080e30804d080d91344720080009a1134226840036420000001342078c20068f83c8ea39000d1f0791d4720000d1f0791d472000000000002000c0018444d12e0022001c00380044bc004002001400380040000202082020c8e191c30106000c001800300046311d021896810003c083810502088e810902108423a0420016308000028e10000018d0212042109020a042109020a042109020a0421096308000000000002116787170e1e1c20e1c2c3840108c6030806088e0308060f0e161c2000c2a808420001c384000006000ad9d40011806100c200000398d4340ca210046000a104a011a8232847308a1c38800000a1e1c4214c6198c22870e2070e19403c386500ea026897c3938708b3280b87080030916112c03170e11438710061e1c3c387871084c3844b00c5c38463143871897c3884be1c40000000000058c20e1c42170e2108020d0e2108020d0e1000050d0e210a470d0e210a470d0e238a4708a1438a47090e1140871000340400000680ac610000004041808201041010400087870f0e1e1c3c3840c398e030d8708061008e01880108c6030806080c1018203040400403080211a00310ee398d410f0e5e1c2c3841c384800e8e40084700c45568e212f4700c60070e1008240048008000184010c8e191c201848009001003470e8e100c20086470c8e100c240048008c62380631a84be1c63570e2e1f47170e111c031000b1a8e215450168e1d1c2a38747088e40080000000584002840608006081c70817a388020801a39002e1f47170fa38b87d1c4c3a8e2000050f0e198c3c386630a041008200000b1a8e212c20d1c2a387470a8e1d1c2a38403080c178c03109b438800184001840018400305e3a1c4011c80000640044ba1c471d0e238868a1c54388e2a1c47150e23 else 0x398e431d8010aa268974392870d0e100ee398d42a89a25816c0218008ee398d42a89a25d0e71dc731a8551344ba1ce3b8e6350aa26897439f8771c4018580080c100c2c0078708ae2af0ee391c76005c384030806112c011004208ee398d42a89a25816c0218008ee398d42a89a25f0e71dc731a8551344b61ce0307870b0e10043c38787083870b0e118c0310021d643ac84800b8e100c23b8d5acf0e41dc6ad6787270e11dc6ad6587230e11dc6ad6787018a01841c387870b0e1e1c206055912c5ac84590305c384911344b2008000b340086a12f8718059e1c5c3840ac8aa2820041642002c24004800801ac8402cb002e1c22cf0e296420e1c3c385870f0e10082010455080010ea01d4020187870802100c206055012c5c38787080001dc731a8551344be1cfc384128046ae1c43984105844be1c4010402080068041fd840000000000068040031c2000000010421080034020002c105820b07fb046801ba010042e384030c9610043c3858708c6018804004055041c3840108021200200000108080082800f0e1e1c22cf0e214020000800808008002a89a05c00401b210000000002584002689113480000a01544d12f87d1ca01544d12f87d1ca0268d910aa26897c3e8e51544d12d8751ca2a89bc3e8e4009610004b2004012c225844b0804b08000009610042000433184020804107f6340ca2100450082280482098e180030004080060000050006000c2225e8f001047800480044bc00425e00212f00109780084bc00400010008063800500044780050004010e0e1c1c3838707080030900114001168e1d1c3a3d002d1c2008747000401841a3841a3840011c24004800900100018384800805008003540021544bd1f07260e11544bd1f07260e11cc5991e0020aa25e8f83905512f47c1c06288e0188800e0e1c1c3838418384800005a38002d1c47168e112d47100123864708004007070e0e1c1c383846a12f071e0e11a84bc1c78387070e0e151c200083238465d1c42008801045091c4238042208200043a3874700040003070e0e191c3a3874711c5a3870709001c1c225a0e2c1c231a0e2002470cc6198c331860711c50388e281c3b1e8e2100440083318a123c004d8f4710802208e01084780840087070e0e1c1c383840308021d1c3a38747000401870708021c1c3838403083470e8e1165471001838418387070800ac87070e0e111c03103470e8e238b070e0e1c1c38388e2c1c225a0e2c1c383840012f07148e1068e1c1c20003070a8e1002470c8e104b2196430386070804191c2010647088e010a47088f010800087470e8e100c38384010ea025e8f83930708061d1c3a388e2001470830708021060e112f07160e1000000500191c2016707160e1d404bd1f07209783886a942478009a8097a3e0e4c1c3a8097a3e0) else (if i < 29 then 0x600140018000012b21b8f4710802c00a0084010ab2100420004200840000b22580231080112b214002004a0194020084183845512f47c1f002e0e118c3838402380628003038450800500060000042c8a0008c010e0e1c1c383850700058384501080118a0008801080015402838002020010bc300042481c500041a81c50006000c0e2380031aa071200181c471001b0c0e00085981c500060711c001c0e23c003040e00085081c500060711c0018a1038a0711c432e8e2100580140208cba38840160051974710802c00a010459800432e8e2100580140208a1000865d1c4200b00288e010a020c04110a00102000c00180000100a2109070dc60108010904120800100a210907080a21080841c402884200424104820004001800100a210a00080c000a00080c000a000c0e2380030a1001200000847018400050008528d2220600a0180280000908e1a0641002c050080141550d0290468e0280270200700470d4224580a00c00001ee3c6b11d1c42007003e0f800b07c00583e00241c00120010a024102c068a0711c40b400000c010ca123885700452384570045c387870f0e1002000c000008631645011c01280810043c38587080600085011c011808111c011008154147100023c00218c5900460204010802101020084500044b1ab220000000000540208003c3c002e1c228006261e0014001004200082a828e2000000180140000200200082a08c190400700c013808008963010011859b183708ea005e8e00a36300c01800002e05800b02c0042808f000e00080023c00000e1a8460000090006000c00000a000c00180028005000a0000084b400001e001400001200000b000e00140028005000a0011a21a84600000b0006000c0018003000002800280050000048005000a001400280000240028005000a00140028000024000010d08d22280000500d08d2228000051a11a44500000a3423488a000014684691140000282c7400563a002b1d00158e800ac7400463a0021a0654691140000300681951a44442400003c00180030006000c001d404d12e002400118e00108f0008771aa1a800900060008c7000a0b0c001800305860b400505860b09b305a003400305860b0b8e182c202860b08b2102c205840000002b8aa85c0040000308000284010f0e1030e100c20085d00b8e100c202002000080080005840208003b8e6350aa268960580280048010e6350ca2a89a258840120771cc6a1544d12c0ba0103b8e6350aa2689605d0081dc731a8551344b02e804006115c55e1dc723001e1c3c3878708ee398d42a89a25816c0218008ee398d42a89a25f0e7a00225d002e1c225f0e215c55e1ec720159846501d8f400ac7a00401dc731ab87201000f0e115c4da1cc72096c009e360054386870b0011e873a1cc723001a1c22b8ab4 else 0x160520e82802804c0200560041303a02b0046a81c6400b61c02600e02b00260020a32002b00461c0560070104d96004158520f0280600a0180400b00002c0500980180ac0081d06c5900081303a0e02d480174380540241d00400183a028854010260740100080e80a2150080141400040a2960581343805401c1401442182802d00301500102802884305005a0074004aaa1c001d55519334850e01500701680154602d00302c05a01002058550003aaaa30729002c02a00f43802000e87014421d0e02d00303405108743802000e8701442a009400405000402d002b8c05a0076380b400c8009001000800808008000104090100300480280c01802001001000400842708c190400b014030040048120088b72cc300b42c2a82ad8c21d641401401801c10aa00480640240311320480230140180060180220180300400200c0180200102100c0119540180230154100c01100c0180200102cc1c010008167460f72005813a3e0f81259902707004002802101401800601802203f07c00607e0f800c0fc1f00181e0288580100500500184e01802322c0300470681383a00422d0010060088270741c1850138c630a8230641001c0400c020040050260538e020060100200200400c0220000280601082cd8c1bd400bd1c05006004c001010011008018023c00202002204ec7010420040030080180440000501001100c10100110260480800900400444004040048000080087870f0e1e1c00130e1e1c200040008482000408003000406080212082410002140011400100420f8022e1c23b8e63530f80158708061030e105822ac00280000170e100020000219403a80400085d90045c384010825008b2008850e1c4014387103fc3880ac8400d42001002106a1c38b50e1c4a870e2d418716a1c388010800c08b3c38a000f0e1004208003c3c002d402002a010000108003550e2d4287000743868708ae1a1d0012b2a80847083500aa01d402002a01020014003a806c700440104681944200b002804116600100418002020834140020400000b8708a00088820904000b87108001ea00088051085c38450e1c00180050a00180020300028002030002016001200180020400c24003000400304060802106a0410806090412082800401c004178528d222018028000080e02ae8f99e410dc2f00430e00e0000102ad8e1ad641505347014014c220600a00c0000181a0440b01401280a00800301402c0065182da80024018018000020b228400300600102000821a8460000090006000c00180028005000004040028d22226a0000140b184080050000048005000004800500000404691113500000a058c300040000c68009000004122002400001200140038005000a00000ac740048005000a000009000004800408004010802100438387070806116)) else (if i < 32 then (if i < 31 then 0x500f004c0300220a8230400a01c064080100121c05c9424a0f8348100400a00a36420300220a82308419028070190200400500c0089230540618420788d903006181e0600c341e00100800880400c01180c00882e06e1103c01800c1381403003000006018018000026001c00203002200460c8160380c0180200202a0640b01c0600c010010150460c80e030060080080a82708c1902c0600c0100120a002000d87004001802108414d400b02807014030040050641083e0a02208117a380a010030030120400318420928e01900600440300222002028082100440c8210741001481400e190420f82808a0061400f01700204e108200290251400f01460a002000c1400400182988ea18809a25817c3e04914001100c008814143001842030023c43001621800b10c0048900c008c270946305050280c00880701801184e0300230840a01462801f4380b80152505013c0080300220a0502340ac00a40055008641083e0881e011030020320941803c0a018033aa010841401860780420ac2706c140280400c01201200800200400105bd1f33c86160500c01e049018012000020460c8200500e030060080090a8190400a01c0600c01001213836ec8200500e0300600800a0841403c0a01c0600c0100120780c0180200140600c0100081574610f3385f0f811d8700400180210840f101e0380c40000508c190400c01c0500c0100121906016954156c610eb20a68e0280300342702c0ad1c0500c0200504c81fa380c028026d1c0500600268e01802301801101e0380c40000501801110010180300400201e0380c40000501801104e0d80c009080080c0180200100f01c0620000284203002001021018011955a3a003d1c051002000827d1c0300481380c008c800900101421484e0a81e0680a60a4271100182c0a0180020004004800005a380a00c004014010007a380600900440801101e05e8f80100f02f47c00807817a3e00403c0b51f00268e028028010270500b01485180a22dc27104e0a0aa301440668e0180240140f40801180a102f4700c01200a81002800c0bd1c481002800c2703c08b1c0701803409007c1a03300409c0fb1c0701880000e10c1b4388e03002001c0a01c0600480500c008c680a0271d0e2380c00800591c0300460500e0300240280701801200a21080d02847181a0508e3018240042ae8f99e400be1c0600d013a160500c02942703c0a018030090138640a8ad000c404100201001200002002000801a0040080020bc2906c140300300801001200800201400100a0208401100501042008802084008c2f0a41d0500c01403008010014178520e8280280062dc2f2a81d05005006004002000805108402884260021303a0e02cc8016c3804c0242e0a41e264140140260100e80ac00da30719002d8700980385e else 0x804800100040080020040010340400030a8230400b00801200004056148470feb20801805e8e0180400800d0072150530feb20801805e8e0180400800d005a0f0200668e0180400800901403004002434400a1a200441100281c05100200082946b590500cd1c03004004a0e1004001234400907080200085900441a00e008c2a91c011a34400801660e00800468c010006008707004001802103001160e00800307b07c0060f60e23e00407b07c0060f01a25e00407b07c00783802800f07004001802103001141a25e0e801307c0040080020580110600e8368d03403991ad6441c85a8d6b203a046964200c00d1104400806080a0080030180500400208f01080108561483606011a38060090090841b4475003347014030058000175574610e3fcce23a86200789605e8f83f00e00425b864118430f8330881805e8e0180400d00003c2105c01196e19058156c61083fac83008815a380e0280300101102b4701c0500ca1080220841b44750033470140300400510010854bd1e8020af03882ce8f1fe6711d431003c4b02f47c1f806859888978380200182ce6711d431003c4b02f47c1d4d1e220080040b3a307b11d431003c4b02f47c1d6cd0a125e8ec0142c09fa3e671002f0701803483688ea028097a380a00b00908401109783885741c410802212c22ba0e209ea3c1c7140c62b8d9a15c50028072118044501388e30a05714500688ec0100500400180210ac2906c140234700c01201200800200400100200082906c140340cd1c030040048021a8c0c00061183208018018040080080c82d2a82ad8c21d64140140180161905a150160380a009c0a01403180200080180040084010004158360a01a0668e0280600800a014600080c20040600020bc0010020008010004158520a01a0668e0280600800a4a005108606000206c5900060d80020040010d400800328c20a0a0000c1414000195526880c004406002202c215747cc82c2af200789a0689605ac2f0580d1806a09540b01a31a820b01a21540d101a18344b10282808509340a01d04600c02802000c0501042008823c04200425b9665568f0016000c00180024c800280026c850009468008055200240025520024002480404d1224000040400134028007000e001c0038005000a00122d001116800900080a00082f0a51a4440500c0240000485591e320a81783e0070ab23c67100340bc00e8380b8000040ab23c671002f0700f00400a00a0030140010528d2220600a0180480000981cc71050718ae3c6b11b1c42c00c02800201400100a2100030580d1000f0280680801400003c0e800a07400403002208c190400c02807019020040050246800c303c0b01c06408020070000121764a1081f81600608406c080120420a01603102ec940fc0b00280c01a0400102ec941b0) else (if i < 33 then 0x110440090bb1c061a17638ac7080a008003004202900205b50030030048030420da23a8018018020020010846108320c018038060100200282ad8c2107f59050110400bd1c0500600680a01882ae8f990561103c4d12c0be1d41083e08a1880143182f00180a0080030042150320b020060160380601002002ffb0c02df8c1df64140440e0324bf1c050068078424f8ae0b02808ba00649605f8e0380a0180400d0000480e01401a0080c02c080180400e0280601002002c2d15c16b400c52c0b01c03008800018a5d0020d02d2a94b2020400816052c700c01000c03006008004014010006028082100440042028082058911340300480000e40042908d1a065110400c02f4701c0300900001c0600020b02908d1a065110434701c0300900001a1b8558ce2005e05801c3748c0bc000028559183d880178160070ab23c641502f02c00e156478ce2005e05801c2ac8f19c400b01b00385591e338801a05e0400a009059110334701c03009000012148360a0180468e018024025a300400180200090d0040018460c82005804009000020800852140420c82006017a38060100200300180524f8364d3b20801805e8e0180400800e0c02ff8c210801df6414d1c050068060424f82848ba006017a380a0180400d0000382f06f470140128460c8200668e0180400800901403004002002000801a00400800228c8013b24c90030bfe3087d90534701401a01210ba048100420880168e00d003d1c018006519002005f718464d0324882006016050060110000382b00044c900241c2148376c8324882006016050060110000341b000483802800c80085e4810030bc2141c617d23838c2926814b40100300b028030088000180a0a0000c2f085448002308507005002055a388102005957320b0abc801e25817a3e0ea68c16004002655d183c0b0abc801e25817a3e0eb6641602f07004003655d1f320b0aa0a81e25817a3e0ebca827e8f99e400bc1c0600d20b02825e8e0280260bc16c1c61782c45e0e40bc1622f07205e45e0e031016c1c01185e16852119340c9220801805815a380601100004347004001e8e008b47006001a8e00882f91d071c8e838a4741c417e0f800c2fc1f00185f83e0030bf07c00783802800c6aa8c4bc1c01000c158022a8f0710d410c1a25e0e00800722d00160e12088015c60308050104200880300a00800400438380a020c2b06c1403008d1c03004804802000842200448100205000111640080100040b002000c010853038003004001002100600105200880100059460024a04bc00694600200500105245802322c3b1a46068c28d8c400a26348c6144c620a26314501391623902898c51408e20a020280821004404f470140410802300c0280800800511e0216c60d827a380821002c0202b0a41403008d1c03004 else (if i < 34 then 0xc2c78c1b855d08360b71c0500500585cf18370aba106c16e380a00a00b0741b366157420d82c0b71c0500700401a1a85c1603a0dc2ae841b05b8e0280380200e0d42e0741b855d08360b71c0500500605c0a41b0580a00a0070b1e3445d071c05004e150460dc2a0841b0580e0180400a00003410006000a00100400105200883986a1101401800003802000900083600a0030bc2c06d1101401400e0d80380200471c014006e8200200700400600a00200400130e0080030416008a0b0060018424f82848ba00600e0180400800b03001105e14846108320801a060060100200300500c01000800800203080101d903080181e3090440082f0a49a052d00400700c02200005842060003200200d01000c82200571d8e200420b0282680600900001c0501042008800d0020068010034009800854d1b322b82325816c3b04c02b870854d1b3248016c3b04c0202ae8c1e058550540f1344b02f875868155460f0aea581743d0540282aa8e9915c5052c0ba1e82a01540042aa8c99a4287a0a80385551d324850f41500700594009800854d1b32c8016c1300768d996400b21d82600ec0041e0358018f415346ec82cc801a05b04c02980086815346cc8ae06c9605b04c029800854d1b32c810ec130070058c0080f035801d0e103580134643b0000100d21d80000815346ccb200590ec130080dc2ae64161579003c4d0344b02d6157460f02c2af200789a0689605ac2ae8f99058550540f1340d12c0b5b0010a9a36659002d87600e07816c380c01b0060d02a68d9992c0b0298701980530010a9a36659061c06600e16300200c2c0040b0180300801600003854d1b32c8016c380cc0202ae8f99058550540f1344b02f875855d1f320b0abc801e2681a25816b0580fa0060b01f400c3415c1492c0b61d8200480490010a9a36659002d8760880400240082a68d996400b61d82201015747cc82c2a82a0789a25817c3ac2ae8f9905855e400f1340d12c0b61d815747cc82c2af200789a25817c3ac1603c01200800800200400130e0080030a8230400700801200004056148470feb208018038060100200302a0a61fd6410030070140300801a00006802e0789101401200c0590020d42b0a61f078100340c00c0200400600a0180200100c200441100282c0510184008371a82a0a71fc6b59c6790c2f87e0181c055d18438d6b38ce17c3a4380aba307b1ad6719e430b4e34c380200102ae8f19e430be1c0600d08d6b22c82802802c01c1ec6840f634207b1a103c03081b46801181840090b0d4606088008b305900382c2bbad5f1cb22cd0061660b200705848009570d0340a81a065007023e0e8360d01805b007d642ac8b2c8816c0140c0048018b205881e0580bc0080f0178010040781602f00203c0b01780101e0580bc0080b01600a0040350b else 0xb0291056148330a82106c16038060100280000d0e4330a461a3b2008))))))
def l3853r9 : Packing := (2989,4,6,0,0,17,0,p3853r9)
def p3853i9 (i : Nat) : Nat := (if i < 1 then 0x4105b04738168407ade8c7d2db4110e0e8f065602fb1002e19e6119988f4432361dac062e8730800ce09e22e8188dc000160c4601a1123c82c3406692a15013800000000f8363014f105b00e7a2a3a8144c19261eb705fa8623843bcc2690ca7834d985941a3984e6a717414d408272ead0567c1f765d7d0bfe88d0184b0149060c088b550243c99f0e8f026944093d27306cc645fc1fce1cf10a2487f38861e0ecc251c052c495661fd0000604840001c5d3102e20388c457f03282e4900b701a1c1223c838000183c0a0210000000030369a5d4000001478ca38000020f9000008172000000000852141f3601b5c6ba071cc3ef045fa10a18655283f218410f9a817fc2c50835000008462c082613ad01b003a800000000e04f800000000a00ff1076876dc06e211f525227130031ce1c430af701d24377e0584046b5470825cc129e02b80000cab744b31261105700000c42080f6182670276000040b010038434501ad0000507ba223be00d8117b8846c2e8a07092e66f04640c200d55028308e58338a153b2e2000038149c040a0c1000030425c19d706c3a086d02cc4ecc25f80003493aa0a2d404383c14270801080d5901520463e47120b6541048411c6370000105c4100fa10c300c80000c225c438d04780003033ea1518400103c7800400000000091c369bbc13c00d450863b20b8009e11ae051dc2cce1c0f41bd1034c16cc17620f8a87da429ea8170121c0253c1fb6220f07c686d98353018180c03174a40900c1e62b11081a896a00002077a03acc94225c20000083e801594225e04810908cb812209a2d718210c336c145d114a085903f2617b8260205044945a4bc810ff86c1882a820ab216f863f8085411401247640f0298a0ae5076d066703c8e1420063985a9c05cc12cb06a4864e29cd453ca08681779048b01c1a4d5a84c7186ee1d510afc0322811de4c660dab024c82c6c23b288f2e3da43c70201709920189c97d01de000000002c164c016b405e88b1827c8007b28b40772c089fc00b2ad602a442460000003b030009010a090109361100001d060301010002000109031a0d0867060327000003090d0304220505020312001f2801080429082e0000042e050802010d0f030a09002e0b3700163916011b086b01010a090201005d2a0922000200031a0106051d0700000d030908360a021b000413000704010a1a0000003f0c11002304232b0100002217030d4f0707010e000900064f03140802054300010011200e000600000972030811050c0585010d004008000013000a0807054a00080234013311142b05120303000f081100005b02000601080303011400036e1a0001150023080300000a02041f0000031a000212011f1a0c000008281638021a160301000000000003110e090101000c0502020b03180210 else (if i < 2 then 0xdf044f607692de986a8410d21bcc02dd8224019760a1007e0888e0bdd400b3058e8193f234911670d2592bc000120350a450e2b600d801b141234c0bf837045ebe11d781976b5cc03db03c80001009e682220408200c0366a0876034a019d846589d470585051bc0496c273070184124138204c120b186300205e0a3c01c916f00001c4c1388dc08720198c1c5d0d0a1500418185c15888405a58176e241b2fdd87a58a346804c24918725cb90c158008468074c39d21070277410e90401422810ad5946e095b41343014c40518206e1c8c24d7008c048f64eab2c90c664c30ee1d0b20ca92c181e7012702178000142cfe0775009fc256427e000022b0501c80000e0b86c6f80000000060e996ea1976dc25a000000002836c0115c1967014303d0000181bd0000000004b5b41d3200bf050c8076208bac539f1ad82da60111c73703de8093407c000010282c185406e423c60081029ac58e10528000300e2851fa011605960419e12f8e26d08b940117d1f3066e95934c1081891072d837e4b8fe80600000000001b86026f0c1fa0fc000000000000608c1441e41df00003869b0359c09151038041a8a94e0a730ff087c2016a006014449303d08a200009106e01368316217a0000181e00001610e7073287abc0312109f11e1a01443e9a05982b63e403c969a0f57068f070ac261c14ec036916fb02efc1706067bb041c1317c60d042885d5c1fe623f0035e84ce02e480ab90d0400e2c0fba056308f0000000008217e05ec054bc217821380c69037781c8511950463052b0057e18660693f1b29828c556b0d2f004a622801923101c18180222c07ed0802957cc17940adde0ad30e10186c1a790f790428407ce559c088381fe012a0000d079407b70432c210307b003ba4488419a00005841443cfc1850025607d702f0c1d79035405ce025760d692a080003c86c0000b02e800034395c1e5f40ed05034075c115a10f186e67087c07b2e068000242dc0000c089800038a76000000001864144920000dc5900000000000aa0000102594bcc00ba5018b006a03976224106b957ef8233c82bf0c55e13c0001016470579c4db443501250000485bc419d21b2000000003422c44ae923dc9562c3740000000010013cbeaa1ae120d09296005f05d800007000d82f2a0a8d2622444e8b5781ff28d620404c444811a32fa2000389118638211f4f498c22ea1c320340a0ab43bad112d102a8719f92e0000809b282cc000004a800000000002bb203300004807800000000009c8121c0001e15b8063400c0c08a000000005855400004005c021b80c8000081be0000000000000000000002025ec0598015008d8000000010839000000000000084c3806f7807fc35f401c00002018c0000000082f0081d400000000000024457315e05d161133305b300400 else 0x612b182d660b752553048204360000c28e88033c07e013702ae1904603acc156e0f1500aa41c6212a32410101abbbfe046724ca073700bd00da429fbf03b82fd8001e012c92cb80aba197c0be5038643c281fa41109816903b2cdabf04ec129c427bc4c7c0dfb020383f741d4610aa830702fa011d80f451462507b21500025e811dc471a1245a45a0028446c643b000a48902421f91dd50930809d40e6e154c0f31a067905984bde0cc584d4b817e06f70ec384a24b10455590abc05a2c0a56083440f600f0e13661f8ee0620749098a65639a42c02494405222aa04df06))
def p3853r10 (i : Nat) : Nat := (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 0xc40a83007fe54541802ff53298c01ffa994c600ffccc263005fe26131803ff13098c017f9974c600ffccba63005fe25d31803ff12e98c01ff9874c600ffc43a630077e9dd31803ff4ee98c01ff9964c600ffcc3263007fe5d931803df4cc98c017f9954c600ffccaa63007fe61531803ff2ea98c01ff9654c600fbd2aa63005fe65131803ff32898c01ff9844c600ffcba263007fe59131803ff2a898c01fba444c600ffcc1a63007f620d31803ff10698c01ff9734c600ffc39a63007f658d31803ff2c698c01ff9534c600ffca1a63007f68cd31803ff46698c01ff9924c600ff449263007fe60931803ff2e498c01ff9624c600ffca9263007fe50931803fb26498c01ff9324c600ff511263007fe60531803ff10298c01ff1714c600ffcb8a63007fe54531803fe28298c01ff9414c600bfd4c863007fe66031802ff13018c017f9970c600ffccb863005fe25c31803ff30e18c01ff8870c600efd3b863007fe9dc31802ff32c18c01ff9860c600ffcbb063007be99831802ef32a18c017f9950c600fbcca863007fe65431803ff30a18c01ff9750c600ffcb2863007de95431802ff32818c01ff9840c600ffcba063007fe59031803ff2a818c01fba440c600ffcc1863007fe5cc31803ff2c618c01ff9530c600fed19863005fe64831803ff30418c01ff9720c600ffca9063007fa88831803ff30218c01ff9710c600ffca8863007fe50431803fb26218c01ff1310c600ffc98863005fea6521803ff33090c017f89848600bfccba43007fe65d21802ff12e90c01ff98748600ffc43a430077e9dd21803ff4ee90c017f99648600ffcc3243007fe5d921803df4cc90c017f99548600ffccaa43007fe61521803ff2ea90c01ff96548600fbd2aa43005fe65121803ff32890c01ff98448600ffcba243007fe59121803ff2a890c01fba4448600bfcc9a43007fe64d21802ff12690c01ff98348600ffc41a43007fe5cd21803ff0e690c01ff96348600ffca9a43007fe50d21803fb46690c01ffa3348600ff4b1243007fe60521803ff2e290c01ff95148600ffca0a43007fc4c521803ff26290c01ff19884600ff84c423007fc60e11803fe10708c01ff17384600ff839c23007f48ce11803fe46708c01ff19284600ff8c1423007fc5ca11803fe2c508c01ff15284600ff8a1423007fc4ca11803fc44508c017f89884600ffc4c423005fe65211803ff30908c01ff95484600fdd22423005fe64e11802ff12708c01ff89384600ffcc1c23007fe20e11803ff2e708c01ff87384600ffca9c23007fe50e11803fb46708c01ffa3384600bfcc9423007fe60a11803ff2e508c01ff95284600ffca1423007fe4ca11803fd44508c01ff18184600ffcc0c23007fc20611803fe28308c01ff94184600ff898c23007fe4c611803fe06308c01ff12184600 else 0xc2c5005fe26162803ff328b1401ff98458a00ffcaa2c5007ee91162803ff326b14017f89358a00ffcc1ac5007fe20d62803ff2e6b1401ff87358a00ffca9ac5007fe50d62803ff466b1401fe97258a00bfc48ac5005fea6552803ff532a94017f89854a00ffc4c2a5005fe65d52803ff32ea94017f89754a00ffc4baa5007fe21d52803bf4eea9401ffa7754a00ffccb2a5007fe65152803ff2e8a9401ff96454a00fdd222a5007fe64d52802ff126a9401ff89354a00ffc41aa5007fe5cd52803ff0e6a9401ff96354a00fbca9aa5007fe50d52803fb466a9401ffa3354a00ff4b92a5007fe64552802ff122a9401ff89154a00bfd4ca85005fe26142802ff32ea1401ff99750a00bfc4ba85007fe21d42803bf4eea1401ffa7750a00bfccb285007fe65942802ff32aa1401ff99550a00ffcbaa85007fe59542803ef4aaa1401fb98450a00fdcaa285005fe24d42803ff2e6a1401ff96350a00ffca9a85007ee50d42803fb466a1401fe96250a00ffcc8a85005fe24542802ff53299401ff9984ca00bfc4c265005fe65d32803ff32e994017f8974ca00ffcc3a65007fe21d32803ff4ee994017f9964ca00ffccb265007fe61932803ff2ec994017f9954ca00ffccaa65007fe61532803ff2ea99401ff9654ca00fbd2aa65005fe65132803ff30899401ff9744ca00ffcb2265007fe55132803f748899401ff9834ca00ffcb9a65007fe58d32803ff2a699401fda334ca00ff4b9265007fa50932803ff322994017f8914ca00ff4c3c45007fa21e22803bd4ef11401fea7788a00ff4c3445007fa5da22803dd4cd11401fe98588a00ff4bac45007fa59622803ed4ab11401fe98488a00ff4ba445007fa59222803fd2a911401faa4488a00ff4c1c45007fa20e22803fd2e711401fe87388a00ff4b1c45007fa54e22803fd28711401fca3388a00ff519c45005fe24d81803ff2e6c0c01ff87360600fed19b03007fe8cd81803ff2e4c0c01ff96260600ffc99303007fa88981802ff53240c017f99420600ffcca103007ee91081802ff32640c01ff99320600ffc41903007fe5cc81803ff0e640c01ff95320600ffca1903007f68cc81803ff46640c017f99220600ffcb9103007fe54881803ff28440c01ff93220600ff511103006fe60481802ff532a0c01ffa9950600bfc4c283007fe26141803ff32ea0c017f89750600ffc4ba83007fe21d41803bf4eea0c01ffa7750600ffccb283007fe5d941803df4cca0c017f99550600ffccaa83007fe5d541803ff2caa0c01f7a5550600fdcba283007ee59141803ff326a0c017f89350600ffc49a83007fe20d41803ff2e6a0c01ff87350600ffcb1a83007fe54d41803fb466a0c01ffa3350600ffcc9283007fe5c941803ff2c4a0c01ff95250600fdca1283007fe4c941803fd444a0c01ff08150600ff) else (if i < 3 then 0x21007fb88910803fec2288401ff93044200ffc90221005ee65010802fb326084017f99304200ffcb9821007fe1cc10803ff466084017e99204200bfcc9021007fe5c810803ff26408401fea2204200ffc98821007fc84410802ff12ec24017f89361200bfc48b09007ce95644802ff12ec1c017f89160e00bfd4c907005fe65c83803ff32e41c01ff88720e00bfccb107007fe65883802ef32a41c017f99520e00fbcca907007fe65483803ef4aa41c017f99420e00fdd22107006fe60c83802ff32441c017f99120e00ffcc8907005fea6573803ff532b9c01ff9985ce00bfc4c2e7007fe26173803ff328b9c01ff9845ce00ffcaa2e7007ee91173803ff306b9c01ff8835ce00ffcc92e7007fe64573802ff122b9c01ff8915ce00bfd4c8e7004fe660738037f33039c01ff9981ce00bfc4c0e7005ee65073802ff32839c01fb9941ce00ffcc20e7007fe55073803f748839c01ff9831ce00fecb98e7007fe5cc73802fd32439c017f9921ce00ff4c90e7005fc64473802ff32239c01ff1911ce00ffcc88e7005fea6553803ff532a9c017f89854e00ffc4c2a7007fe65d53802ff12ea9c01ff89754e00ffc43aa7007fe65953803ef30aa9c01ff99454e00ffcba2a7007de55153803f7488a9c01fd88354e00ffc41aa7007f65cd53803ff2e6a9c01ff87354e00ffcc92a7007fe64553802ff122a9c01ff89154e00bfd4ca87005fe26143802ff32ea1c01ff99750e00bfc4ba87007fe21d43803ff32ca1c017f99550e00ffccaa87007fe5d543803ef4aaa1c01fb97450e00fec41a87007fe5cd43803ff2a6a1c01ff99150e00bfc48a87007f666233803fb13119c01fd9848ce00fcd22467007f664a33803fb32319c01fd8918ce00bfc4c467007fe26233802ff32f19c017f8978ce00ffc4bc67007fe61e33803ff10f19c01ffa778ce00bfccb467005fe65633803ff30b19c01ff9758ce00fbd2ac67005fe65233803ff30919c01ff9748ce00ffcaa467007ee91233803fb30719c01ff9838ce00fec41c67007f65ce33803ff2e719c01fd8738ce00feca9c67007fe54e33803fb28719c017f9928ce00bfcc8c67005fe24633803ff12319c017f89760a00efd3bb05007fe9dd82802ff126c1401ff97360a00ffc39b05007f68cd82803ff466c14017f89160a00bfd4cae5007fea6572803ff330b94017f8985ca00ffc4c2e5007fe61d72803ff10eb9401dfa775ca00ffd3bae5007fe65972803ff30cb9401ff9955ca00ffcc2ae5007fe5d572803ef4aab9401ff9945ca00ffcc22e5007fe5d172803ff2a8b9401fba445ca00ffcc9ae5005fe24d72803ff126b9401ff9835ca00ffc41ae50077e5cd72803ff2e6b9401ff8735ca00ffcb1ae5007fe54d72803ff286b9401ffa335ca00ffcc8ae5005fe24572803ff122b94017fa9958a00ffcc else (if i < 4 then 0x5fe26130802ff32e98401ff9974c200bfc4ba61007fe25d308037f30e98401ff8874c200ffd3ba61007fe65930803ff2ec98401efa664c200bfccaa61007fe65530803ff2ea98401ff9654c200fbd2aa61005fe65130803ff32898401fb8944c200dfcc2261007fe5d130803ff2c898401fba444c200ffc41a61007fe5cd30803ff0e698401ff9634c200feca9a61007fe54d30803fb28698401ff9434c200fed19a61007fe649308037f30498401ff9724c200ffcb1261007fe54930803ff28498401ff9324c200ff511261007fe64530802ff12298401ff8914c200ffc40a61007fe5c530803ff0e298401ff9614c200ffca8a61007fe50530803fb26298401ff9314c200ffc18a61007fe48530803ff422984017fe994c200bfecba61005ff25d308037f90e98401ffe774c200ffebb261007bf99930803ffae698401ffd634c200fef19a61007ff5c930803ffac498401ffd324c200ff711261005ff245308037f90298401ffd714c200ffeb0a61007f74c530803ffa6298401ffd214c200ffcb8261005fe65c30803ff4ee184016f9960c200bfccb061007fe5d830803df4cc18401ff9730c200ffcb1861007f68cc30802ff32418401ff9720c200ffcb1061007fa88830802ff32218401ff9710c200ffc38861007fe58430803ff26218401ff9210c200ffd08861005fe65d20803ff32e904017f89748200ffc43a41007fe9dd20802ff32c90401ff99648200ffcbb241007be99920802ff32a90401ff99548200ffcbaa41007fe59520803ef4aa904017f99448200ffcca241007fe5d120803ff2c890401fba4448200bfcc9a41007fe64d20802ff12690401bf98348200ffc41a41007fe5cd20803ff0e690401ff96348200ffca9a41007fe50d20803ff46690401fe97248200ff4a9241007fa50920803ff322904017f89148200dfcc0a41007fe20520803ff2e290401ff87148200ffcb0a41007fe54520803ff28290401ff93148200ffc18a41007fa48520803ff422904017fd9748200dfe43a41007ff9dd20802ffb2c90401ffd7648200f7f33241005ff64d20803ffae690401ffc7348200ffeb1a41007ff8cd20803fdae490401fed2148200ffcb8241007fe58120803ff26090401ffa9944200bfc4c221005fe65110803ff32888401fba4444200bfcc9a21007fe64d10802ff12688401ff89344200ffc41a21007fe5cd10803ff0e688401ff95344200ffca1a21007fe8cd10802ff32488401ff99244200dfcc1221007fe5c910803ff2c488401ff95244200ffca1221007fe4c910803fd44488401ff88144200ff8a0a21007fe50510803ff26288401ff83144200ffc90a21007fc84510802ffd32884017fd9344200bfe49a21006ff20d10803ffae688401ffc7344200fff19a21005ff64910803ffae488401ffd6244200ffe992 else 0x6ff5cc818037f8e640c01bfd5320600dfea1903006ff8cc818027fb2040c017fd9320600dfe41903007ff5cc81803ff8e640c01ffe3320600bfec9103007ff5c881803ffa6440c01fee2220600bfcc8103005ffa65418027f930a0c017fc9750600dfe43a83007ff9dd41803ffaeca0c01efe6650600fdeba283007ef59141802ff926a0c01ffd7350600ffe39a83007ff58d41803ffc66a0c01ffd7250600ffeb1283007ef50941803ffa64a0c01fee2250600dfa40a83007fe64141802ffd3298c01bfd984c6009fe4c263005ff261318037f93098c017fd974c600bfe4ba63007ff25d318037fb0e98c01bfc874c600ffe43a63007ff9dd318037fb0c98c01ffd764c600f7f33263005ff655318037fb0a98c01ffd754c600ffeb2a63007df95531802ffb2898c01bfd844c600ffeba263007ff59131803f7c8898c01bfd834c600dee41a63007f720d31803ff90698c01ffd734c600ffe39a63007f758d31803ffac698c01ffd534c600ffea1a63007fb249318037fb0498c01ffd724c600ffeb1263007ff54931803ffa8498c01fdd324c600ffe99263007fb889318037fb0298c01ff5714c600ffaa0a63007fe64131803ff12098c017fe990c600dfecc063005ff26031802ffb2e18c01ffd970c600bfe4b863006ff61c318037f90e18c01ffe770c600bfecb063006ff61831803ffaec18c01efe660c600bbeca863005ff65431803efb2a18c01bfd850c600ffeba863007ff59431803efcaa18c017fd940c600dfec2063007ff5d031803ffac818c01fbe440c600dfec1863007ff5cc31803ffac618c01ffd530c600bfec9063006ff60831803ffae418c01ffd520c600ff711063006ff60431803ffae218c01fdd310c600ffa98863007ff4c431802ff32018c017fd900c600ffcc8063005ffa65218037fb3090c017fc9848600bfecba43005ff25d218037fb0e90c01bfc8748600ffe43a43007ff9dd21802ffb2c90c01bfd8648600ffebb243007bf99921802ffb2a90c01bfd8548600ffebaa43007ff59521803efcaa90c017fd9448600dfec2243007ff5d121803ffac890c01fbe4448600bfec9a43005ff24d218037fb0690c01ffc8348600ffeb9a43007ff1cd21803ffac690c01ffd5348600ffea1a43007ff8cd21803fdac490c01bfd8148600ffa98a43007fe641218027f93108c01bfd8384600dfe41c23007ff5ce11803ff8e708c01ffe3384600bfec9423006ff60a11803ffae508c01ffd5284600ffea1423007ff4ca11803fdc4508c017fd9084600ffc48423007fe9dd40803ff2eca0401efa6650200ffcb9a81007fe1cd40803ff2c6a0401ffa3350200ffcb9281007fe58940803ff264a0401fea2250200ffcb8a81007fe1c540803ff2c2a0401fb94150200ffc98a81007fe0c540803ff242a0401ffa1150200ffd4ca61))) else (if i < 7 then (if i < 6 then 0xe64073802ffb2039c01ff9901ce00bff4caa7007ffa65538027f930a9c01bfc9854e00ffecbaa7005ff25d53803ff92ea9c01ffd9654e00dbec2aa7006f720d53803fbae6a9c01ffd7354e00ffe39aa7007ff64953803ffb22a9c017fc9154e00ffe48aa7007fe64153802ffd32a1c017fd9750e00bfe4ba87006ff21d43803f7ae8a1c01ffd7350e00bfe48a87007fe641438027f93119c01bfd848ce00fdf22467005ff64a33802ffb2319c017fc918ce00ffe48c67005ff64233803ff12119c01bfe7760a00dfeb9b05006ff1cd828037fc66c14017fe995ca00fff4cae5006ff661728027f930b94017fc985ca00dfe4c2e5007ff261728037fb0eb9401ffc875ca00ffecb2e5006ff61972803ffb2ab9401bfd855ca00ffebaae5007df95572803ffb28b9401bfd845ca00ffeba2e5007ef91172803ffb26b94017fc935ca00ffe49ae5006ff60d72803ff906b9401dfd735ca00ffeb9ae5007ff1cd72803ffac6b9401ffd535ca00ffea1ae5007ff64572802ff922b9401ffc915ca00ffcc82e5007ff64172803ff120b94017fe9958a00dfecc2c5005ff26162803ffb28b1401bfd8458a00fdf222c5007ff64d62802ff926b1401bfd8358a00ffe41ac5007ff5cd62803ff8e6b1401ffd5358a00ffea1ac5007fb5c962802ff922b1401ff99058a00ffec82c5005ffa6552803ffd32a94013fc9854a00dfe4c2a5005ff65d52803ffb2ea94017fc9754a00ffe4baa5007ff9dd52803ffb2ca9401ffd9354a00bfe49aa5007ff24d52803ffae6a9401ffc7354a00ffeb1aa5007df54d52803ffc66a9401fed7254a00ffec8aa5005ff24552803ff922a9401ff99054a00bff4ca85005ff65d42802ff92ea1401bfc8750a00fff3ba85005ff6594280377b08a14017fc9350a00ffeb9a85007ff58d42803f7a86a1401fed6250a00bfe48a85007fe64142802ffd3299401bfd984ca00bfe4c265005ff65d32803ffb2e994017fc974ca00dfec3a65006ff21d32803ff90e994017fd964ca00ffecb265006ff61932803ffaec994017fd954ca00ffecaa65006ff61532803ffaea99401ffd654ca00fbf2aa65005ff651328037fb0899401ffd744ca00ffeb2265007ef911328037fb0699401ffd734ca00ffeb1a65007ff54d32803fdae499401fed424ca00ffec8a65005ff24532803ff32099401ffd904ca00df6c3c45006fb21e22803fd90f11401fee7788a00df6c3445007fb5da22803ddccd11401bed8588a00ff6bac45007fb59622803edcab11401bed8488a00ff6ba445007fb59222803f5c8911401bed8388a00ff641c45007fb5ce22803fd8e711401fed6388a00ff6a9c45007fb50e22803fdc6711401bfd7360600dfe39b03006ff8cd818037fae4c0c01bfd6260600dfe99303006fb889818027fb2840c01bbe44206009fec990300 else 0x3240691f008f524741239511b748d7a46672328117c48bb445c322d6115108a2444c5223c111848894443321fc10ed086e04359218610a90851a42492102907b8831e416620a79049881b240c220511022c807c402720038ffc07fb23f831fa40fc7c7e103ef11f688fa347cc83e3b1f090f7a47b4a3d731e978f46079963c6c1e0b0ef6c76d43b0b1d5a8e9c4743639c51cb78e4ac71aa387f1c148df706f1e37301b7a8da7c6cc8360e1adc0d5d06a6034d11a468d1d868ac340919f48cf246752338919950cae46490322818e00c5a862943133188e0c3f061ca30ce18408c1845ff22fd917e10be885f162f2c17788ba005cc02def16e30b6bc5a7c2d30168c8b33059582c95163f0b0a057922bb215cd8adec56382aea155c0aa8454a82a3d150e8a81853cc29c614d78a5885284292b148a0a3f451de28b4144a0a11c500627ec13e189d6c4e76271b136709b004cf8265c12fa097984b7a259d12a8094c04a2024f01268091c44848240411f208f1047362345117c08b60455e2298114088960440421d910d8086644304216b10a10846441e020be1034080fc40501fd20fd907e6c3ef61f640fa207c483dd21e930f398794c3c541e0a0ef0876bc3b0c1d150e7f072e838c81c4d0dfb86f38376e1b6a0da506b8835841aab0d260676c32d4192f0c8c063e031c218ca0c3a060782ffc17e70be805ee42ed817550ba385cc02e4416de0b48859c42cb416430afb057a02ba215c30ad60560c2ab415430a69052ec28ca141809fc04e1c26aa133e097884b4424f61252091d84794231e117808a7844e0223010c20836041542058101507ff03f9c1f220f44079683b801d6e0ea00744839c81ca40e3b07120375c1b6e0d7c06a98348419f00ccf064a031ac18060bbf05b902c9415b00a8b051f0273413000933047302240108607f603d481d940e0c06ef03438199c0c8e05cd02b7014600a0204d8025c0128409020461022080f4007600351019880c4405e202bf014f8089403b001b800be8049c020e00b100440015800013fd9720e009fecb107004df654838027fb2a41c01b7e5520e009fec8907004ff64083802ffb2e41c01ffd9720e00dfe43907005ff65883803ffb2c41c0177d9520e00fbeca907005ff64883802ffb2241c017f99020e00bff4cae7007ffa65738037fb30b9c013fc985ce00bfe4c2e7006ff26173803ff930b9c01ffd945ce00dfec22e7007ef911738037fb06b9c01ffc835ce00ffec92e7007ff64573802ff922b9c01ffc915ce00ffcc82e7007ff64173803ff120b9c017fe991ce00dfecc0e7005ff26073802f7b2839c017fd941ce00fdeca0e7006ff61073803f7c8839c01bfd831ce00feeb98e7007ff5cc73802fdb2439c017fd921ce00ff6c90e7005fd64473802ffb2239c01ff5911ce00ffec88e7005f) else (if i < 8 then 0xd5e3eae8a572c2b8995be8ad9e569b2b3c9595cac58560eaafd15796abab55c12adad562aaafe556f2ab1d553caa8755382a96553f4a9da54e1aa6b152aca936548b2a3fd51aca8b654392a0b9501ca79d53c329d514e56a70b5375a9b2d4cc6a60452eda96ed4b24a521525ca92654886a40851f428f4546d2a3495194a8c2545aea28a5127a87e5437ca168509fa83ed41b6a0b2504da81c9406e9fcf4fd7a7dd13eba9f3d4f8ea7bd13da89ebd4f53279d13c849e2b4f05a77ad3b4e9d514e552709d37d89bb14dc426d5936369afb4d5ba69cd34829a184ce1264fd31d298a54c35260992fb297954b9fa5c7d2d9296464b17a57f52bde95e14ad3255652a84952b4a782526928f494634a26250d5283c93fe49d8a4e45266493124974a4a0524c2924a48f5a460d22d89155489aa433520b8903c480e240151f3a8f3e478aa3afd1d088e644722238911c088ddb46dda36491aae8d01465123209188e8c0345f622f3117588b9545bf22d9d167c8b1e4568a2aa114a489f344dc224f9121888ec4446a2149102e87d343cc21c310d9086964336a185d0bee85bc42aa214d10986847f422fa1049080883e441eb20ed9073e838841b8a0c4905e482ae414ba09dd04d282404114a07050354815440912040901e880c2403aa010cffec7f6a3f739fad4fcf47e483f0f9f76cfb527d773eab9f500fa527cd33e3e9f078f7487b8d3dbb1ed58f5ee7aaa3d499e9f0f4827a2a3cf31e5f8f27478ff3c549e0e0effa778c3b9b1dc7cee1076a03b449d8cceb6075753aaa9d3b4e8f8741d39f59ce9ce690733139649caa4e512723c39171c85ce3ee71ce38bc1c560e294713338899c384e1a6705037f41be48def66f1c37511b90cdbec6dd636db1b580da806d1736849b23cd8966c0735c21ac28d57a6aa6351f1a878d36c699f34c89a480d20068e934691a2c8d136688d342919fa8cf5e67a133bc19d60ce82672a338999b3ccd82664732f419690cb1a651c3282993b8c930648132351902cc7a0638331ad18cc4c62262c4313298884c3ba6187309d18390c12e6038301097f08bea25f3a2f8897bc4bda25e692f0097760bb5e5d352e6b172b4b91a5c5b2df516e74b6e85b302d6d16ae8b4ec5a202d00166a8b28458d12c4b161fcb01c57c12bd095d74ae8c57262b6c95ae4acfc56282b04157c4ab3655842aad95510a9ee54ce2a5b9525ca90054572a1714f84a79453aa29c094d84a61652fd295c94a88a504526b292114888a428520628fc14784a38251aa28b794560a1e050d9283d1418ca086502c27eb13efc9ed24f40279493c009dd24ec92754939dc9c784df826cc935e49a224cf1265213258984a4c0e25fb92ea897144b7325ae12d3896804ae1256992a1894de4a582525128a8943849ea24e99261892cc49342493123889196486 else (if i < 9 then 0xf42a04be3d1e044280309702210cd46531964a04b639080400510900001b1e044219660442195ca0c781108a4d81108668f1d8fb359e85409ac723c0885006b8d34d948b418e8000208480000cd065210090000338db2d02851d8e4201201250210086e36cb409747639080480492d8e420110d065210090053438db2d06391c84024026a4bb51b6a8b0542c2a0a34faaa77d539969c8b4defa69fd347e996f4c85a60152f6696f54ab8a543527c6923b48e2a41dd20b6901b476fa3ac51aea8d35467aa328d17ca8b9345a9a2bbd1582893d4400a1de50bc6844d419aa079d032a807d4039a0084fcf27d3d3e1b9e91cf16277993b919d3ace8a2731538c89c4b4df766e9137289b25cd88a6c0535be9a9dcd32a690d34549a15cd02e6747337199ad4ca6263e3312f982dcbfce5f5f2f4797984b9065b112d56964ecafda571d2b5c95834ab9a545b2986947d4a14e4f11274d934a4976e4b412514927ec9112483723fb91a148c8a44e5222e9107487ba427d21039071c82ea404b1fea8f8b47b923ce71e268efa4770a3b0f1d3a8e88c72a638dd1c578e12c703a36871a818d1a4685232a519328c89461d22f4117808ba2c5c4e2db1168b8b11c56a62b1315608a4f4518e2779134b895244a122361117e88a6444b22207106e8819c404e1fb10faf8791c3ba21d250e728709c37621b950d1a8630c2ea215730a7e84e7425be117f0884842041e8a0e09069c8342c16ea0a6f04fc82264108e06d502b180f34071a023f00ff8027c0075fec8ff3b7f4a3f989fc4efe077eabbf2c1f8eafc3a7e0d3ee39f6a6fb187d6a3e9b1f3aef9ae7ca33e499f1faf89e7c16be059efecf78e7bb73dbaded18f66c7b1d3d6ddeab0f5387a8c3d29de890f4317a0d3cfc5e7a2f3a879bfbcd59e570f22c78c2bc355e026ef6c7786bb9e1dc44ed3c76613b1b1d7aeeb4b755fba861d2f4e924747dba349d152e84173feb9f2dcf68e755736db9919cb50e4ef7255b9179c86ae3bb719c38a8dc4bee21270d538599c20ee0b1701bb7f85bf70df356f8f37a25bbe8dd446e8db72a9b818db386d87b69e9b328d9596c983626db0aed8376bd135c11ad92d6736b29b56b1aa1cd4ca6a4335175a790d345698534b85a55ed2746906346fda308d1406851340359f80cf6a679333b419cd0ce1b66fdb357599fccc846632331119794cb74659cb29dd94aec9f864bab24119192c7f563b931d018e40c65e62c9b15198998c4916226b109186d6c2fa615b309c984a4c1d860d7b05f58284c09b6010aff997f56bf8b5f9f2fc317dfcbef95f63af97d7c5abe1f5ece2f4f57a28bc7f5dec2ed9d7502ba4f5d0a2e5fd721cb8ca5c50ae0556f36b7575b7c2db3d6c86b5c05ac2ad5056a30b48c59fbace1966a8b319596aac9fd6476b1ee58d9ac4c16190b05758202be1 else 0x2c7018e8e80000ce787a38cf463c3d1c873b1b64b350c3d1d8f0049a8c6596861c8e060021a0c7018ca14740000987a38b0f47107ca187a392c7592ab40a187a3b1e009a3b1d0000202c848000101747161e8e2c3d1c4e331e1c8447198f0f472364b387a390aad02861e8e5b1d66a04bc3d1d8e4280249787a39088c70188d1e3ecf409a0863a1c0c923a000034391c4684391c6872388ae87238c9ac74391c84526b1d0e4721a2c759a81358e8723c01347400007472100866a25e1c0c471d1c0436c9668e022340a04bc3818ad02851c04435194c6592a9409a4b2390804006109002329549a4b21009007fd98cb2502591c84020024840211ccd4652a9349642010012e3212000040290846ab1d66a1478110a0083540884334195c6632c94096472100800b212000038110846832b8cc759a851e0442802bf66832f8cae55e813497c72100986a31b64b3d02812f8e472100800c329549a4b21008c4201088480000e0442140884239d8db259a851e04428024ae55681409647210080092120000381108502210a0442115caad02851e044280218e80140824b810a0412a93497478110a0073415c9ac7239080400410900001c08842811084682b9358e478110a0084005c60210082420108d065210088552692c0446380846a3418cb25025d1e0e470310800c3420046831964a04ba391d0000498cb25025d1e0e060020d0e3018ce66a3418cb25025d1e0e47210018687191d000029a28e23558eb350a3c1c8f0041a8d10719a1c6592812e8f070300126823a000043441c4687198eb350a3c1c8f0049a8c6d92812e8f07030012d90188d047400008688388d063838ce7636c966a1478391e0093518cb2d025d1e0e060025a00311a08e800010d10711a20e20fc1c563ac955a050a3c1c8f0049a8c6592851e0e060020d00311a0aa4ba3c1c8e420020d0474000084ba388d107112e0e23418e0e33441c455838ac759a812e8f0723c0106825c1c6687198c8e072118d0474000086871d1c8e0229668e470110a1472380886825d1e0e470318d1472380886832b8d34d948b418e42400017fb71b65a0c721200ee34d36522d063a0000871b65a08b639090000438db2d0c3d1d8e424021c6d96861e8ec7212011fbf1f67a1c7c3d1d8e8f1b8fb2d9e83438f87a3b1c84806195c6d96831c84024021c69a6ca45a0c7400010e36cb418e87239090083438db2d063a1c8e424025c6d96831d0e47212010e36cb418e872390900871b65a0c74391c848041a3c7d9e831d0e473fecd4632c94096472120000a2120046a34194c6596812c8e42010016424000061f811087e3b1f66b25548b40a1c7a3c08850069a8d06531964a0472100800afd9549a4b23818840200248402131c848000109605210e0442112e044219660442195604421f8ec7d9ac)))) else (if i < 15 then (if i < 12 then (if i < 11 then 0x1e0e474018af5025d1e0e47801dc6632bd40a047039caf071194af50a391c84020020d4632c95ca04da3c1c8e42002c9a80115c9b47239090000398cb250a3c1c840039360e23b9ccd45726d1e0e47210014e326a0000426d1c46a26c1c8e43538cb250a3c1c840041360e226a0000326c1c46a31b64a1478390800826c1c44d4000064d83889b0711cec6d92cd428f0723c012576851e0e420018a04d4000084d83889b0711409b07195da050a3c1c8f0039348e8000109b478391c84da3c1c8e426d1e0e47215c9a4ba3c1c8f0039a89a4b2381ca57681409a4b2381ce4d8388ca5726d1c8e420100106871a69b291681368e800028d0e36cb409b4723a00009f1f67a1478391cc68f1b8fb2d9e83409b478391d00c3438d34d948b409b474000146871b65a04da3c1c8e8049a1c7d9e851e0e4739a1c6d948b409b474000126871b65a04da3c1c8e8049a1c6d9681368f0723a013e34d367a1478391ce6871a69b2d026d1d000049a1c6d9681368f0723a0126871b65a04da3c1c8e804a7db2d026d1e0e474023c7d92ba45a1478391d06871a69b291681368e800028ae4da391d000031a1c6d9681368f0723a0125726d1e0e474018d0e36cb409b478391d0093438db2d026d1e0e474024aed026d1e0e47401fc7d9e81368f07239cd0e36c95da04da3c1c8e805068224d2591c84003c0000225c00003b1c6ab311a851e0000412e0000191e000019a200001936000019a2c71aacc46a04d63c0000a351a0ca632c94096472100a000061a8c61f2cb40a04b2390805000031a042010ec61fac95422d02851e0500002cd4632c9408e42014000096390804321000502210a0442000e04421408842b1d66a04ba3c0a0000412e044219a0c6592812d8e472100a0000591e04421c0884223c0884381108468b1d66a04d6391e05000028d0650d044840031a8c659a814097876391c0c420030a003210cd4630ff64b211a8140964740001811a81400c47180c477399a8c659a814097872390800cc384d55011aac759a861e8ec78020d450c38dc60311df0e23bb8cc759a861e8ec78024d4630fb66a04bc391c0c00536406239e1c47a31e1c673b187db259a861e8ec78028d450c390a0057198ca18721158e031540a04d25e1c8e420020a1871141164b19430e20892f0e3319430e32861c563acd409787a3b1e008a812f0e36380c4872388d087121c25763a1c8e428018a04d438ec759a81358e8723c0101fa8140840240000e420108b3502800886a31964a04bc3b1c8e062100164b0190860863a007fb3518cb25023a000080304c6592861c8e06001dc6c7018cee733518cb25025e1c8e42002f0e171d1d000022a8d54719aac759a861e8ec78020d587a38dc6c7018e8e80000cef87a38cee657198eb350c3d1d8f0051a8c6d92861c8e060021b else 0x3c0146a2a940978780183e572ad40a00b40001055a81430e42ad40a18721570ec71994ae55a814084020021c69a6ca45a04d25b1d000057edc6d96812d8e803b8d34d96831d00003f8fb25548b438f87a3b1d2e36c955a04b63a1d00871b64aad02692f0ec74025c6d96812d8e82212011fb3518cb2502591c848000289680118cb2552813497872390800afd9dce66a31964a04bc391c8400612f0e27192d000022a8d44b19a8978719a9c6592a9409a4bc391c840059a8c6d92a9409a4bc391c8400596496800010e65925e1c873f1d8d34d92cf42a1c7c3d1d8f0069a8c6596813497872390800a6812d000021409787187cb2d025e1cb63ac95caa91681438f87a3b1e00c71a69b2916831d0000412d8e800010aa4d2582d8e80001cd4e36cb409787a3b1d0093512f0e32a9349787a3b1d00771b64b2d025e1e8ec74024b24bc38cae55681409787a3b1d0093518cb2552812d8e872390800b3518cb25528134978723818840067ecd0652100800625a084773518c34590894097472390800cb1c6ab311a851e000041aa00001868224ba391c84003c0000225c00003b1c6ab311a851e0000412e000019943411a390800631964a04ba3c1c8e420024d507238dc680118cb25025d1c8e42400013472389c647400009472388d563acd428f0723c0106aa3c1c8e471c1c447400006d98388b24740000859a3c1c8e4b1b64b350a3c1c8f0043420e223a000032851e0e47207cb3071d8eb255681428f0723c01307095497478391c84003c1c8e223a0000325d1c44ba3c1c8e4a3c1c8e383860e18384ab07112e0e471b8e0e232d1c8e4201000c474108d468b1964a04ba3c1c8e42002cd08011a2c6592812e8e472120000a6841c4684000061f838ac7592ab40a1478391e0093441c468b195497478391c840049a08e800010974711a0c7072390970711a20e4719560e4719a0c64ba3c1ca6a3458cc647039ac663a391c8402001cd463ac94097478391c840051660e4719a8c61fac9409747239090000586a8e47198eb25025d1e0e4200220e13b9a8c7592c94097478391c840061660e23551c46ab1d66a1478391e0083541c8e371c1c4d0838a0e18386c61fac955a050a3c1c8f00541c3592a92e8f07239080088391c44ba38a0e10d12e0e3838497478391e0052ac1c563acd4097478391e0082c92e0e335564b24703960e132d668e472100800723a0846a31964af5025d1e0e472100161f2bd409747239090000498cb35025d1e0e420020af0711dce66a2bd4097478391c8400595e8e23558eb350a3c1c8f0041a8af0719a9c659a812e8f07210012578388d4630fb66a04ba3c1c8400515e0e22bc1c4578388e7630fa69b259a851e0e47802d3457a391d0050fb64b257a3c1c8e804540a04ba3c1c8e420020af07115e0e22bc1c45725d) else (if i < 13 then 0x802049642000f0e125e1c0032ce1c455c388978711a8d02831964a04b63a1e00a1431c0231406822c7238080074391c46843800687095ca08723909a8711a2c759a81358e8723c0a000058040020f84822d02861c0500002424d02800800563808003010450c723808005b1d66a1472100a00004010840180000a6a31964a047030060081609b471accc47200b04e1c09020140000f1658c355908d411a0ba3814060200801c048100600002818090200c000060240803000014500900c0088723812040180000e048100600002812040180000b02800006020009a0001068220a0431c8e050080126832f8c35d908f1c840049a0cbe30d76423d0e390800a3578cc61aec96423d02871c8e4200360000140000225c0000334197c61aec847a008210014680d04410c723908008800005000008d11a8891e0000331e002341963511214000073b9a8c61a2cd40a04b2390800b0d5409a4b2390800734194355021000de30fb662350e3e1e8ec749dcd5e331868b2112812c8e420030d0650d044840031a8c6592a9409a4b0591c85000030c6592812c1647214000092582c44b0008d4e331964a04b0591c8500002c960b178cae55e8134960be3c0126a3187db259e8140960be391c85000038aa4d2582f8f003364960b19cec61f0d364b35085d1e0000587cae5508b40a04b0591c850000303e572a845a05085d1e00005068224d25800a5726b1c8e4280000e6af198cb2502582c8f000028960517ecd4632c94097876391c840059a897871b8d8e801fecc6592811c848000205816861c4504000061f2c9430e4b1d64aad02861e8ec780258e80000c16163a1c4e3c3b1c6683290804002a08277399a8c6592a9409a4bc3b1c8e420038ee6af186bb211e813497c7002cee73351549a4b05f1d00925a00477399a8aa4d2582c8e42402bf67a3b9ccd5e3ec95caa4d25f1f0ed2b955a05025f1f0e4721001477399a8aa4d25f1f0e825a000030892f0e32b95422d02861e8ec780258e80000cee733561c9870fecf477399abc7d92b957a04d25a1da5726b1d0e4721000e77399a8aa4d25a1cffb3d1dce66af1f64ae55e813497c7c3b8d5e331f64b3d02812f8f872381800d3b9ccd4552692f8f87412f0e23518eb2592812f0ec72390800b2c92f0e33518c3e1aac964a0472120000b0d56458709dcd5e331d64b25025e1c8e4200303459c38cd559138f0e24892d0036861c587087da05025e1d006b187eb25548b40a187a3b1e00b0fd64b20b40000c0b09aab259c392b259c38c3587131d0e2c3b1c46832d64b24201000e8209a8c6592b956a05025e1d8e4721001a1f2b95423502811c84800028c659a861c8e42001cab8711dce66a2b956a05025e1c8e420030ab5011570e23518c3ed9a861c8e420024ab8711570e239d8c3ed92cd430f476 else (if i < 14 then 0xb0018a187000ca187158c3f5908b40a10bc3d1e00005d4002001d430e001d430e001b8cc750c3800a1f0d364b20bc3c000086c966a00bc3800c1f0a845a05005e1e00004855a05005e1c006b1d66a04b05e1e8f000025a00d6380481a0883416c723800f5043800668a821c8e4a821c4572821c004a80358e8723800c68b1d66a04d85b1d0e47800016d06380466832908050000190400154084001b8ea1871d4104420010cb50c38ea18711430e205e1c85000016a00bc3b1c005a8208468a821c750411086168892c0a0180000e638d166225023908030048e0ee2ad1c6b321688e40a10b05e1c8e06214000125b8c055630d56423500602e8e0500801c16a842c030000182d50858060000354217000012a00b00c0000551d40160180000d5005800616a842d0e0180000e16a842c8e0180000e0e0580600002d4217000010cb1a888240a42014000091c2a14b630d56423500651d040200801ce30b5421606028060000485aa10b028060000382c0c0541400006a802d8e0500c00007a842c12060280600004069b211a80140200398c34590894096472100126a800006240d76423d02692f8e004891c6630d764b211e814097c72390800e800004638d44600002c003000c6a224d25c000060d0449a086391c840044000028000051a889348f000018d4630d16422502591c00971c000038000050000098f0014000022140000331964a04ba3c1c85004364100119dce66a0451e0e472140000a0411c003350220e4721a8d02871964a04ba3c1c850058a0100118220e23b995c663acd428f078000146a3187c34d92812e8f0721401608008811071164110719cec61f0d364b350a3c1e000059a8c61f2c85c22d025d1e0e4280302e08008ca008838c1107158c3f592a845a050a3c1e000059a8c659281341b478390a00a68034100121549608a3c1c8e428000121a088228e0700181047000c1107238c1107000c1107238cb2088391c8088391c64b0451e0e4350208e0780000c1f0d364b2082381e0000487c2e1168140104703c0000a1402002332d1c840280000c1a088228e0721000e420009c608838d0442000c110710220e20441c4088391c00441108003340a010470390a000040208e822110c71a2c9409605210060095baa834110451c0e05008014088391c03000018d42871c68b3112812e8e052100600d0441c030000160f00000cd4632cc44a00d02908030050220e4700c00006050220e0180000ca30441c8e0180000e160441c030000195428d1c6b321688e401a0a0401c0d00003c1207030150500001db208a391c0050451c8e00206822d00451c8e0500801242008006683286822420018d4630f96424116812f0e47802c24d0008ec61fac95422d02861e8f028000186a31964a18723c00ed0638046552692f0e4721400 else 0x29f2b850261248b4120502582f0e47030148402008028264d051a14b058250e040120000c108500b0221401007108500b02214010078140100355099469a4ca45200943810048000340b02802008a302c0a00802858160581401006179a347992be401a0b04b1d0e47030148402008024aa1328d349948a4016c70200900006a1c0b022140100643816044280200d02802006654d2441205212000087181405004014041031c0a0280200a6a31964a04b0591c8402400016040100500002808268d1e67210d04c1c0c038110802800039542751a65208b0480d00005018028000115427d198f3259c81421a4b83818070200802073151a051a310e67210d04d1e0e470340884010048502751a65208b0481c0c02400018b7598c05a2c550a8516351d6533504822c1347038180a03010050000c8180a0140000b2804c1c0d0040196e681428f3259c81421a4b838180702008020aa1438d3290458240e060120000c5b8a01307034010071441e008022ccd5a331a6720508692e0e0601c0802007aa8502751b65208b0481c0c0240001ab3940260e0680200eba1409d466304c1c0d00402a51078020086a13e8cc7992ca421a4b83818070200801eaa1409d46996822c1347038180480003a50098381a008030a146098381a00803ca20f0040105a6ad198f3259c814117070300e0401003c5868d1e64ab90058268f072381a0442008020aa1409d4699480240e060120000c030140280001650098381a0080303d16098381a008038a04ea3318260e0680201328068260e0680200f284a834130703401008078260e0680200cb7340a04ee35198f3390068260c058139542751a65208b0481c0680002c6027d1e67200d45d1e0e470300d828018bf62a3478c469fec867a01005f1c0e04019080401400028aa51a6520870301006024000162c14d8c3b590a5411a0ba3814060200a0001003014850040140c05214010050301485004014260a638140842010040095528d32904581808030120000b0521c0c05214010070521c0c0521401007098281287030148500402414060290a008031a2050040100c01400008024000066a888470e408e1c4638fc46a110c3d1e000048470e225e1c00308e1c5110892f0e408a1c41143889a87147e2350881358e8723c0000a718470e341108411c3883e120894021872140000908e1d8e34110800308a1c41128208844258040030d0449a4b2390800731964a1872390a0076cb400233b9ccd4632c94097872390a0000661c00235068220b0014d5502580086aa861c6e368004677a861c67732b8cc759a842f0f478000166a3187c34d92861c8e4280283ed968004873a861c67a2cd430e439d8c3e1a6c966a10bc3d1e000061a8c61f2c85422d0c391c85005855a0011f8c3fd908b4217c7c3c0121a0ab40a0))) else (if i < 17 then (if i < 16 then 0x10fe642a13090470e0581401ab713895466310e642a13090470e05813a3e1488d4220502692c17872381a04420080201409c40a00680200e210a441164b034010081389546630a04e20500340100b108502710034010071408428138821c8e06802014271288428138801a008048a34621cc85d1a0a63a1c8e0581401a28881411a4d0501a008048a2210040105025f187fb21208d4015c703009000070480621689f4621cce42160ac3818070221005000080b555e351f6533d0480301408e3a1c06800043f62af188d3fd90cf40200f05f1c0e06028080280004c0c01400008270782c15c7438180a030100500c5509f4663cc96720508582b0e470300e04010044ee34398b4d42ad198c43992ce40a00f8592f0e47034088401005c5a0f0320086a13d8d47594cd41200b0551d0e06012000105bacc643016aa8556351d6533504803c180ba3a1c0c0501808028000668e06028050000351c0d00401068aa7198eb299a8240160aa3a1c0c02400020b73b89e8e0680200f478020062d3568cc699c8142160ac391c0c038100401039aa84f6351b64b3504802c154743818048000456673a381a008032e8f4275198e8e06802013478020062d3568cc621cc9642a908582b0e470300e0401004868aa13d8d47594cb40a00b0551d0e0601200011190842b470340100713a8c2b47034010070ad1e008020b5556351d6533504803015474381804800043f7e3ec857a00f0682f8e06028090000709c140602a00006a38050000202e8e0680200a0f05d1c0d0040185a2771a8cc799c80330e05812d46630602e8e068020105905d1c0d0040182a5005d1c0d00401c5a27f1e8fb399e86401b0b0431d0e0601c0b0111a2a84f6351d6533504802d8e4703009000080c01a0a4391c0d004020d02813834144703401009068290e47034010072b85c1a0a4391c0d0040245ba3cce401a0a63a1c8e05812c1e0d058288e068020100d802006345509fc76351d6533504802c15474380d00008aa84fa3cce42160ac381806a1909f47990ab4120508582b0e0601b5a0c7018c1080000cd4632c9408e0602810840200a0000d32a6922090290804800024ca9a48824028030e4582b5568cc621cc96720502582f0e4703014840200802a05012006650e04c12050210804010028562651a6932914802c128702009000072dc5e2c550a43a140280802800030d4058110a008032dcd02632895c6a3318873259c8140960bc391c0c05210080200b8e554e34d2652290058250e040120000e02c08850040160500400cd065f1e8c38572a84fa1902692c1609e3e1c0a042100b0154f874389a6ca64b3d0c8140960be3e1c8e06029080401c0002c65098240a042100b00813075b21648a40160943810048000343a058110a008030983a058110a00803966050040104 else 0x71a1ccd42ad1e64af90079341b0ba3c1c8e0621004014170acd56351a6ab29948d41200d058280e06022090000a2dd663216aa8556351d65335048034180ba381c0a8200a0001600a00003169a94ae3518873259c8140190ba3c1c0c420080240d062006345538cc69aaca65235048034160a038180882400026b786936008028b4d528d198d3e1e4d365339028032174783818840100503c0d062008735558d46d92ca46a0900682c14070301104800049670d26c010055d28e1a4d80200d0d8020062d9468c429fcc95c2e9168240190ba3c1c0c42008026aa51a693257681429a0d0582a8e0703011048000486421869360080328c430d26c0100686c0100316aa9469948a409a0c0501c0c044120000f178368e4780200ca306d1c8f0040183c0d05d1c8f00401c5e2e16aa851a3cce409a0d85ac6428d1a7f32570b84d22d0481409a0d85e0200f068190043287027472381408420100400b680360e3070340280228d349948a4117474120000a5bacd54a34ca41174703a0900006200002554010035538d349948a4117474120000b5bc010035b9a14ae351f6733d0c84368f0780201caa51b65229045d1d048000296700400d74a36cc0100559ca3469f4d36533d0c84368f0780201caa51a6932d045d1d04800029a100400d4700400e51a34fe6522d0484368f07802018aa51a6932914851d04800029000014010024591e0080228e00801b641b0040112a0d8020084d45c01004160aa46e38d465b3118834017076380c8500004455238d4642d118834017076380c8500003c692a91b8e32d90b44620d00602e0ec70190a000090bc552371c6a32d90b44620d0858298e070190a00009ca8d02813b8c471a8cb642d1188342160a6381c064280002a349548dc71a8cb66231068034160a0380c8500004a55238d466231085b1e000050a04be30ff6424116802c15c7038180500004251250f845a01081400009fd8c85a2a14097c6238fc6bb2190c447a0100783015c70381805000064572892b8db2d00631e040200c0000d174941ec78100803000024703594495c61f0d365a00c63c0804018000203894495c61f6c845a00c63c08040180001e3817495c6d96803c180b63c08040180001e2a14097c6230d7643211e804017c703810040100485a6a13f8cc7d92cf40a00f0571c8e0601400011170a4341107814040100240c018000080600c00004030060000209fc7d9e803c12c70300a000058298e4703006000038280c0180000b000008d4630d16422502591c0400505026128802b0e0601c08840140001be30ff642411a804017c7038180a0200a000103bc7c281309446a1102812f0e4703408840100456e3216aa83e1409046a01045d1d0e060280c04014000281409c40a00680200e251085027100340100812c42008022ab462) else (if i < 18 then 0x82b83a0062f1538cc69aaca642c91a8241160aa381c0c04412000144d41d003178aac6a36c9642c91a8241160aa381c0c0441200013198aa8f0723c0100783c0100348c1d003178aac6a34d565325568141160aa381c0c04412000131551e0e4780200d078020062f15c1d0049568f32162ae401e4b05d1e0e4703108020080bc2c8b8391d006180bc5a2ab1a8d35594c861235048030960aa381c0c044120001725d1c028000145e2b9468f3218c822c15478391d82f158aa8f0723c0100817a2e0f00401460a383c010051a8c01b0780200c3010a54aa0d83c0100871c1c0c8021943813a391c0a042100802005c1c8e05022090066cc1c42f6cc1c02802a000029b9a8d02892d8e4621cc96720508692e8f0723818840140002c39550a4d027b1a6bb2990b247a0904582a8e06022090000ad8d3491a3814028000205091400c68aa1409ec6234d565325568141160aa381c0c044120001594401003148a10031658e47990b157200f2582e8f0723818840100445aaa1409ec6234d565321848d41200c2582a8e07030110480005c0280000e50683191e008034a1164b80200b28340348f00401a50214a9541a4780201039550a04f25b1c8cc799c803576331870274723814084201007000069a0510719a050014012666a9468cc71f8d56633902843497478391c0c4200a000150f468b30723a00c2af188c3e1e0d56429d00802e8e0702808028000483e1e0d741208ba381c0a8200a018aa9468cc71f8d5663390284349747838188401004a3507400cee6a154a346638f87a35598c96720508692e8f07238188401005c3d1a2cc1d0053541c8f0040163507400c3d1a83a0082cd1c642c55c803c960ba3c1c8e06210040100f059170723a00d078020061e4592e0f0040194707802008309468c3e1e0d063200d4582a8f0723c01e1e2c92e0f0040195428d1c6ab3192ce401a9838190033284e8e4702810840200801507238140882401a0e19468c43992c95e23508843497478391c0c4200a00013554a3466310c7f325988d42210d25d1e0e06210070000a1dc5528d1c7f32570bc46a1108692e8f0723818840100516e32180b458aa1558d46210fd6532180b846a01045d1c0e05410050000d0862e5783c010065b9a94aa310c7f325988d42210d25d1e0e0621004013f188535d92b828134703a0142cd1c7f3311a8440a00f2582e8f07238188401c00026212b85e0f00401946212b85e0f00401c6128d18843f992b85c2a1106a2c15478391d0115b8a04ea571a8e3f992b85c2711a8440a00dc044ca1c2bd1c8e05021080401002c2f0710b4d5a331e64b257c81401e4d0683217478391c0c4200a0001616aa9469948a409a0c05018088240001c9a48814028000185e2b554a3466310e64b390280321747838188401004c5e0d0620087 else (if i < 19 then 0x4800044ee9a489340a01401cf4771a1ccd42af1e8c439aece64ae162a8549a4b05f1f0f80b0ab46214fe64ae550aa45a0902812c17c7c391c0c4200e000163b9cc55a3cc858aa1507934960be3e1f00f1a0a9469a4c95caad02852c17474381808824000245085c010041528d349948a409a4ba3a1c0c044120000f00b017004010f4771a1ccd42af1e8f3f9aece64ae162ae47a19026834960bc05c55a3cc95f200f2683416c74391c0c4200e000113b9cc55a3cc858ab90079341a4b05e01c7a3b8d0e66a1509fc7a3cfe6bb3992b858ab91e86409a4b0582b8f870360366a1578f4663ece64b3d0c8140960be3e1c8e0601a0803800058ee731568f32162ae401e4d2582f8f87c03c2c0f2582c0c8031e8ee73350abc7a331a7c3bd9cc964ae162a853a19028134960be3e1c8e05210050000f858a00b2390802800020ee731568f32162ae401e4d2582f8f8702805011169ab46638fc6ab3192ce40a00c8592f0e4703108028000543c590612d0051a8abc6230f87835590c853a01005f1c0e05010050000a0d43e1e0d56433d04803017c743815040140406a0c400c7077350abc7a331c7c3d1aacc64b3902842c9787238188401c000301e8d16500451831003f185923d005f1d0071af8c3c1d0d5642a91e803417c740001c355568e3f1aacc64b3900661f00c1ad64b20c05c010070f058170040143c0d062008c703200665ac96426090281084020080161d0281104802b430e216e8c43992c9542b11a8440a00c8592f0e47031080280005555a3318863f992cc46a1100642f0e4703108020090e0ee2ad1c7f32572a856235088142164bc391c0c4200802ab7180b5542ab1a8c3f594c854235008030174743815040140002eaad18843f992a854230bc3c016310ad40a00b80200e650e540a00902810840200801615c38bf632180b455e311a7c3bd90c95c2c14e8040184b05f1c0e05010050000d0d1556351d6532572ab40a00ca582e8e870301104800050aa9185c01005161ab4663cc9642c55c81401e4b05b1d0e47031080200a0b0d5a331e64b3902812c1787238180682210040123287026090301408420100400b2581408824014d4632c9408e4200a0000905a000031a0ac552371c6a32d988c41a04d85d1c8e060240a0000a0b0552371c6a32d988c41a00ba391c0c04814000121548e351988c409a0ba391c0c048140000f1a4aa46e38cb6620d026830174723818090280002430178ae5528d198c43992ce40a10d25d1e0e4703108028000585e2b3541c8e8030b857e351a6bb2990b247a09006a2c15470301104800050602ff188d3e1d0df643214e804017470381404014000289a48814028000185e2bf1a8fb299e82411747038150401403e8e8010b8576351a6ab2990b246a0904582a8e0703011048000528e0140000 else 0x7ec582bf188e35d90c85623d00803417c70380a000098e4542971c6bb2190ac47a0100682f8e0701400012fdf8c2b11e803417c780246a2af188c3a1b0d3642b11e80401a0be381c0500004c34d90cc561b0b83c0a000057ec55e311f643215e80401a0be381c0a0301400012168abc6230d764321608f40200d05f1c0e05010040131678cc71aec96623d02802f8e470310a00008006000018e45e2c0d044160500801239350a44ee38d764b311e814017c7238180a4280002601800007e30e86e23d02692c17c702c0171126814030028bfc71aecc47a00f268298e062140000e03016000021a8c61a2c844a00b2390800a160ae546ad198c43992ce40a00c8592f0e470310802800054586a0612d005f1a8fb2990c247a0900671d0e0602209000087ec622f160abc6234f87437d90c853a01005f1c0e05010050000ba69220500a00006188bc582af1a8fb299e8240180be3a1c0a8200a0248008c4188018b0556351a6ab299681401747438180882400023004008556351d65321848d41200ca3a1c0c044120001100a000031783100371b1c0c80219438130481408420100400a0281104802365a18718b1b2d000a00a800008d42ad198f32590b157205007934960bc391c0c4200a000153b8a9469a4ca45204d2582f8e8703011)))))
def l3853r10 : Packing := (1253,3,6,0,0,17,0,p3853r10)
def p3853i10 (i : Nat) : Nat := (if i < 7 then (if i < 3 then (if i < 1 then 0x540e0500430010103c0607018980a000682810020007800230180c32000300000042b03806120700c000600004520400010140002000000d000881c480087804020100000000000402000093c000d0001000020e82402213481408131980078020003000090480018050d04802000e06c085d0f8ac060302810143202000080005050160200868000006844480c0b01000000e00c2e000b8080c2c000780450310001a0101800042a008200003000040212120081002091800208128600a07030400014018140c020380414440100416400600c0c010b81c0000000240000148301c020800014070383c74060585c0e010a81418030000034050000806050300004010b8002420018100c0c080380a000303c00020a0001a232a000021b00020420303000020105808100a00000001b0600000010087c0014110c8241100020001a00b0c00010082c1e1d0204802042181400072987c000e0001806070880000080102804020000008010200c0802038201006000c00c19008007e030901c0000000080a02008783a0200804340019878502d0300032010000000020200000010683c0c0f0780c0400030106a000003c0c01018040207000bc54031f82c2600020008c170281032080202810010018822000f80404000882c0002028002008050dc12040000800021780c5802378002e010800c00004701c741302000000305030280c03820000e0080404000228c0202000a42a00008444e010100000600000002000200027080683c220910000020c040000e0007824120306831382e018100a04060081801260e808003c0080c0c008002c0f040100c07018040401000002c021691c0a000909064290180c3a1b0b8140207188000006000083e0103804301b0003c00000002402060089000010c93802020200022060083016030780846020a0dc0c000e00c4c071e0100c00230841635000100016050544216048201e0c010d40432020000202090000a01040a044200100c000d078bc061a0f8140a000d89c1a0a010000c020000002003082404140b00c1801000002a5b07808ae00158184e002281010111400020110080006000683004220580000300000024100201402130182cb4010e0001202030203c021e8d800400b010020a0a81c000000834500008950041a088285c0b028000000008383a0910000142000800040b048140e00008247a000086c0003078144458018341004218440c02020180e280888c2a340000c00010e80400100080004080087412020005898040f018be01020000a0f00820080c0000420030287c06282983c0002068001261000281c1500000062b1789400180000000020082026180008000000417800030a0102a0700000022d01840040303004002c09000340a0100820000688802040186810190a1280203 else (if i < 2 then 0xae082ca94cbc368b404a1856329911b0da9019a4081a189dcbeacf2010d454cf100e9110abd50358497d7cc58aecc2d884093705fff0edb20fb944fea099720809c2e15c11538a87615f8a28a48565c86e840524000000000318c632974a81ec0000208ccee440007864cd30000000000a083000003844a42706e2b3a4993800001eb44c4f740000070519024800000000068432f2537adc8e02cd152fc7171a84457c16bc99b0704dca2767c1fd98a0ba164722ca7c5b9a89001168fa109d8b1c909daa21d76685300f148544728a5403ed081ab829160d0e01f408d3521420f0ca8821d041bd716ba7161e88067442200000f869b68078c97092077a3421417cc03fd0720fc155820e194437699239297ee4764100978495c0d04b0359c017a999300896458d4400e10106f11deb1db6c2bae914981550a23a4a2a819645a03318639b000c705ad902ed01b70432f39b7f92d85e1b46cce6e93dbd0e5f22abc453b8879b9136d61ecb404f085a2c0d6c6278000002840d5214ae0ec81800028480a094180c06001a8000413000085e060003c223505860120610808540a0380000040000c0e001186440210001c040b021f406070207c5a1c08810080e010240c080580012000580400010881002080286826000003406030701c0a02078241e05030000003130000200131f06208028040c100000430030f8081c01068000006058000c051180056140080c240b028280c020002808030a014260a0400034000783400000782034090600000180186800010491c280e028040803000d80c13000086816028000c220400414000e0004c08000084c00008dc1203038000600070003e031308c0c1d090000c0a0200c2203080481c0a21040800004170040b03810001300804280e00064000000844000202800000d0384002131384c020500018120801810000e0c8000a070681800000502400091800024000680434010c0040206000001404050002c000280c00290118c38340180408000c050162601000060a130547613000040c1e3e0000603000101203010641a240008c060f11808240a00000020a0303c46000983c040404064fa060485804070080c060000048020e078042c39080000c1f0005808022a00002120107c06061e06800040280c0600008000a30020400200000000a182304416100180c0006040040a070301800020a80c02000001c000400030001b020300c02018783002078000c01090003810010182a080082c4605000100a2501840020f0f0003602128001406160740c150088c000e0381470000483c0002040849c31228000420048000c250a81402380000034091000c1411008040205098b41e151a80400213901ca009018301e0a00884161407008000211858000f02038a4000000008010580c000f0000004110000 else 0x3d80000000000000181818000030310000008ba980000b205b800a0000038795503660000040e1f0b8901603a226501b02078c313a4466508511901d230f012159d029ed16ee3029dc02a80440fe14ef2e34502aed0119824dd088804eabc53fa83cea099f50af9485e08932b090120a237961589631e160c1a4cc42760631304e1a14050d85845604278aa628302d1886a96322400627c45e70242141b0e52be8a712010fb148a411890560088179265e04364037b50949009ba02552850a707195607a426418188a879e527c0f15ce845dd1add10ea2818b3643f30ac4c0cda30431c081097904e3de8682989506040b62cae84e930266d035962296423470cfe519a9d08cc882ae48ded05a00122120c5982c580000c14ba809b10239f02dd00000602740d11387c2a17409c15789aed88c17c1844000b02fa604f06083a6c2b5426df85d2b05a400002c540800009e2f6a58640000613852e43f60667e35d7f53bd0427a192f4424305ba4040622727058bd82c3f131e92bccdc39d480320babe1929caf80860c82ccbc5c03c33b40a1120ac6e1f5b4ab93015ff120931567849f7058ca088a822f7c0a1d02e2d2597a07d7b0ca60b30036868222f854fd80f63173c26b8642e8792fd9160d01ddbc17b38418805bda5ce78b8db032d513ce01b6000007054d72306e005dc42abb0da06154c02af49c7080a3721e4c5fdd83d5d1382501442c2e58b14104d8e02c5228ee01cbf969ee6d2560adc0461502b39244abd673c57b7841ee0b286239fc0d4e05309036562c42943a4110000001a1c6103297041a736db61f38006c00000e23ec848e0000050a2f404f7811ea4204e0731910f940182495d69413d060521bd00000693af00000000000000203b30000000001c010c8918d0c660000344d2391c33071362cf68134582b1a2d242068f4583e00b5309bf080400000000000000108328c0a90000000c16c24ac794e3063772c4b219928542402567b09d46c4100f59008ad24d9603376433c82aa6068201ce349e7c1208380a984ece40c74014981248e2bc5c104b83f2f12b7a244800004862b00001c15d800004127c0000000001f9230000000001c2dd74122b8859e0c78a1e29c1fea8334504b4cc01d0bbe2f059c1241f8713854bb90be6225e06721b2b28614b2169044f0bb81db87633607e8259fc3e9612fed13b006b8ec2266066bdc49ba1e9085d1914023005b42cb242745054cb02a0a4cc3cd38f034080fa2ce1bd0143d074400000e1fbf09664133ba121034f10425300000212736289a800fc08ab92c3604ec3a2b0e8020410d020763021ba755fb077301fdf4220715d93114d2038683d2a90d07225d6199983e6b8aa020861203a649ea6870110df6903394db1690296096d460ad8b1c3937c70f94a2d6ab1e7b084fde43aa05)) else (if i < 5 then (if i < 4 then 0x17b0bfd5cafef8047c54bc3255402030347085ef98a9b41cf5c3e2f837fa3371ea1fc0000784f42042e41d6c000018a6fc14ac0000004b8000001080400001d4d10000000001416e10486f81219041e0a2980000504bf32d9e20ff9804b0000050ef7a0315c1c0d85e2b865400001005f8000062d58000030158480a1f0954c21cccdb5100ea034e6a447405c328254a04a40c108cce610905d0234000000000182ac0000002dbb433dec9c1641dca141584481c54f82f0e84f47ca241976f4d24c41015036ad85e530ebc0612304b480000d40fba1e2c4cddbe03ea11317151400000000090eb8808ef03e220a859296606634c1648000000a5bfc897423ec1837215ac00000088fd029900000222a400005055d2134104e06403d80ba771518c47959012ba02900001e025000002023d00000c69e9c5922986cd80ad6571104ff6045d50e9480ea0c041709bcf0dca044c2829e001b9000000000000000000000000408d0f0035884dc0c778660245b3786cc535e1c1614000001b710000000003cdb4899711277362ad800004144dd13b7c181fa957705e100000c2c8989eff007a028ae00001ca088977770f4e627c4045ca074c10ecaa20e2c0988000010d8e061bf39adb0955f4011e2b7939aee048382072c041400002851730f30000018b8ea883c80d7000003c4b200000886ac620ce402fb029b0000089c8f047170148216bd81b5b496700000f08b400003f95c0000000b948096c00002004ac0233e055983091190fb169ce0e62cb9b685c3bc7a201bfdc04a9849359369c031900ea78b61e12f184b90905f50a6920bd77ebae852be188d307b7e06a802e0596ef805b4e42480cde781457257ec275103d1b8455227b26495309e0b305bf3392e07064d716131bb307f405454531e067db00eea0cdf4248f8911605a1e293cc36ea833db0bb08191c8525a807230cb400001f82d50471a14c30030ac07e80000520b0c135f41d5284bc5e9b52067802c86977100fe88184000007081e50136c64738144e950db3058208cdc0b180000a13c600001092fcd3b240beaa24b88b270e3ba2eaa800001c9dea003d8111800002808a18791fb43b40fa1c955e4558122542206682a5416ecc0ee36427000005989600001e27894223a082b0000165384000000000b21b4a18fd82f1b805670f76a073b0146b52f0416f000001c294902550000041779c56d7800e041052128404d310510801028585900dc704ef21064605e4c304c056190e6a000024d22f01320000164eb40000502f9b14886c117c27b0000000001e048202b5607cc8419bc1551c80320ae80000101ff80000589e5a2464a2bd402e9a972d0000000003c5724843cd1233e81c3c1afd027ad0632e41f5481e80000b0753e62564ae8908a30000000002088f672baa1376000008d else 0x940da45f28197800001054fc23c82068f893ba038580e3889dda01c5d8dfb59259cc3a37112e045ca186484e7a08d4d0f9e612b8022170293d048d4209f812e3faec4c7c2224c1c503613b4505fa0000000000000080c6bc23ac80c580000e07a40000000004a33b00001e6729e06bd048d127fe4509ec18348645d07c5403b50227638741212144dc485acf0410c35bcc660b45191905e0030ec16ceb1e99184c008a5028e7c1b8104a98259042621448f4949a0069402d0e8825000a660d2301611c8ca886d2115d600533483a189766141f21c39818070161e0a6a4237ec20ab017d224cf256db454a39a9bb06d3391b342278898c71679e00e04274902f7f0fc046d3d439321a697edf92149a489a289c700577c5ff400efb84a0b0216809770586d20c510d940000281bda8b0432cbf22d9400004814be2f5a8655bc09b7101a000004479ac4b60000030d1e400904cc72073cd04f378e8780a7880b4c40d3605f34506601049164ba5a7f8243b455d21523e01ab099300803d066601e52443bf09ac360ce0000344a3081774135a22a08447e80000a8b6400003c1b6f0b46c16e85c437c58d7300580c4ae18a18263601f70e19b213b50028a8b9008ed72678e09014015c214b94827d82a3495c00000011519c2d469a11860db3158941ae78893004402803eea226089e14174c2c15b22d284220000000000c1e2460fb703cd4658c89d4580d770ec5e1fae84c59009c308cf21a31c50dd84698610f217124327480d0b076061d9bc8a8185cf304e66249a8cfd8000060d123202c098760b9f509cf611cb79112052ed098745e574580589b1304cf8235ec49b820dd52e7491b5983ab4033b650df61e58000051992c0cc20004b434bf00d1531032217d84f488945d05b96281541c9ce04b326ea62106c1d0680ac00001a0b6d425420851013d8e4110c51a218eb50ae088372835538309e4092213bbc1cea0069336bbe23d8c9ef01632436ae828d4054c088f8f112f61303400398380e2b096808171dbb0257000019925e01768c52802eb3019a2852c91b15d4124c0ee902a2fa06f5125f22e114265a85d7f135666d08457f80034413bc824058463a812f616c0a0609c1957040a605a361d00035768b45000000000104010000090f6e00002344ef8539332dee2e5800007830850deac01e64ab1220c0000000000343f280010b08d1a2500c81980000a2c9b60fcf03d48000010df400000f2389198340594e0843046d164b900001253ffc9bf10425c12e6b8a8b423680000f14a461fa9c20b48b4430dcfe0e9dc044000007003761e7ebacf9811f00001005958c35e82b89c4e1800464cb24831ac215f02b6d41e780000d10ea618f4c55ae8417e05e48502402d8e13a2000017515e8db6697c3b0eab426c183b85018670d020000204320a) else (if i < 6 then 0x40b50383309850d2e40c007409e260067720eac0c95050180000a044581ca8faccf87f59106c00000e2b2a8747f618520ebc0000100c84173200000089fd082393072e19cc858e601802227745170c3d7c096578ce441888856791087d12db649cd402cb009232106e1ffc41c87016af26e80000304470000088ace00000c1eb80000b312ec1ad70503b8a7a000000000000001867a0000086d11c375319cf12e782256481c6c0915b104dc20c40431c9235e1578e610685ca9092c21755002d9016369affa111400003809e583f5b347642438000051116f0a28c15880000780e800000a2bbd8b9fb04d1100cc00000000031a6b4e7f7622d100248830ac04282166400000000082ab8e08c6c33901776a07b9e05908547f87834085f24eb9835800000012c401c7409a9008ddd41b5014eb0a15e0852525cd0419c448ee038210da6064f745444884500000a47a6448300000b287400000c0b64099cd1048e0398425c00714d11c6e03d280db00000130c901efec9783614042e6e4234c0000288deb139d85d924230809caf122e61b09c485d9b6f8099ca6a070106b99f50000020a0b41e822066f263be1492a19230646a32ccc263680f63e1bc20f710272c00000000000000867e40000000000000100f0dc9d1c13b200000e417400000000000000800f20532800001e6a4c537d05bd584f5914780245000002c2bd00e38e5774017a8061a9039380b4f4b5f599400000000002b24c480db80a1c00000856680000e10a000000000018640c06f3a0cd6091b2843b450e0857c6c2e88000091112a0c7d8352f852190257e4e9bc5a9588c992fce24d78000028588600fb62a1ac3733055ee00ea000028183c1770000012542c80019043103259a056c4d4bd8330686be00003046c0000062459243c440b0681f1570e1a64824b58f20a800001c153c00004805ae037561b0e100190a51c01b420e13cd7dc961c20911a2cdd71e8106a6c0c69080bc583e707e3711496110e033cd0b0a9100e000018585d86fd6119c01c4d415030ac9a0a13e0f140000506558132546b1000000052262289c245b02613837880826e2b4d0207189afe0bd5012b3cdbbc84fea611020c8e85b188b2652dc838159c300da7a44033b7034d83f820240f26f70143c74768892840b3d214570408c8b08a1136dc120c05e8000080b120557c04650835ad052c02c56022841a9a00000c1e3681e1606af000000000000000000000000000010171a06f2c0f1e64c8bc0371065152a10252ed501e00b3be11c080f778bed3019500e7362a94d576e1660b24e4a082cccf2102bdd259b207fadb6d4753ca2d04e10ac4b09e84fd6361982aa80000702a2802af617b80000282280000080b0800001887e92f22000010b8f68b0e207792108c057eb0a16d0003c1a7405c02908cb else 0xa43903052c908ee2044c057db08fb20ed1014fb84ad0955bd3343a2864459a38982628b6411230077188d2d058f629d549ce38b7db11a0e23aa0441c84dc014d0418e94281b0a5b72691c25300000200982169e06dfbd0593045f12e3e80bb88399f047690fe600001824d28b6980e48c12790905e199d106c8c1500000020175d21b7e0163c462c85e73049242e2dec4ef04f2332e1423e68276186da907924240c180db0b710118c80f7d41761033e4eaac916b01c3c716bf0a72c01568010f784fa516a2455994023620283117e00001836ff83ad12b73a8258000030746830ca80ae7caacc0b38f32a685c29c00b4073b83129e42c0c4bd306ee78213641f3c53119222f0b5ea492c0000283e0e01c72820c01130000042116c26ba0447e09410000041264c1735881fe15e6b40b80000002642138806e1e04765086004015e00b3896300947410f56c2912441e883a60e7d40c0400001880611044000018311ea0a000000c20a2c589f037e00fe4e1b34c12c113c3a128960d76045f2852bc153c22705c04758a41b113864ddd825f080e49110522d294579207e6635f45c162d8470f2b90000085c46c9bef02d600000a267543b00030550438000019000f87dd42d3181bae486af9976501b360e47c82ab03a1615aff1db185812e3d220a50bcaf2c34a987e8f278d25e3149ee107eee296200000000068108000006284983da9817e416bb20ddbc1643845810c55460c0453c10a098005d605eac1a5e13941053b016fe44dc28b5750a26053a6c253e02bf00000c2a88c5ac78ba806158c1da40515c03e30000060893c18271496616eec1e0a832c0093cf372c01c59807030225b083325e3a13490087670b4fc4d6e4bc989398130d12541083100000040c61dc140d06cf8b835369c415b203d1508f3f0b8ca1776c4a8c0a2cf26b0e29bb03214843af0d1ae407284b58000080318426fe853f00000d0244000000000613bc6015d202c84805cb0b4d2dd6e25d1407aa8315b2185a1f8b818c00000000006190d896fe01d1203c682357009391230c152b8225144b8996e63220720c99495a009ba814f6e03100000789096009a60669c2dcf054b707d2c217681f331828beb36e4dbd4d0f20b93802306607ec5a808a92e034fc4d994086c02067076c40dc484618800650914ac2dac4f5000007f29824bba8450c955ab0f02002e7c231f089a50675216d4a02cf1887f00d762603037f009347065840fff413bd01b5f3249e1c425825600559045385332c0676876ca083ec5a87c3fce41c4202bae6dd8439d79145807c804a65c576a4821c3373c0722c05438a9000001c074341938892ae04d285ab7c437d1297c1297428b5428000000e1058010fa0452e8ab160ff0a14c9845998888412b9a4c780160697f9a05c12c2c78bc4e91eac1749))) else (if i < 10 then (if i < 8 then 0x772027d27e580d5f4aac109850e4516051300ef401e060dda64e79042d8f5887c48881a5b412fb04c5d10cd219884157d0b6766db30419b04caa0b91c0437215e0c0ee1152e70adec6d42facec49509305ac81a14886602b40000180640ca27f0a47b153820758d02e2048660ece212de08388042c72652b960fc5aaa06567069b814dc00004193c000000000041a2189a500000c6463c400d88b5102460000383ad503ca502b400002834d610fc5173bc2127b1d380000333a2c1f54000000000000000000141e0d8896000000000171e6e039930b6c000004a4450830c02b2019d049df886b200000dd629735a0000090e2441ff30bc400000b1664c166103fd889609076b881958197290a0d0194e1047086a3f59e3151b0017500d7a01461e21c99167042c79032000008160d3a5eb84653262be1de8430e20950615dc0000049b608204c0df8e0a53e97cd00f9f07f020766902ea8ae990a23a02c5c19e181e5b222e065b44c09f8a016245d65a97c10c986f8c1569e40c04324c1a130c821c1a43001280000d143c00000000048153586c2c502bc0ead9347c6139bcff3021480000140f8a05a30326a202202bdc0000183f6487c0000004167f387fc8b9a501e0a10a8000070b8820435620fd0c3c696aef0dd9481e6480280000f0e3e603fd0a08403b13090b206f100b3484037006de490bc0717192222d79a1739c39b6027cf10344165c84fac88e640ab9e1f910c4fd202ae237e66a61421a282cd72658c40fd8478b8552c0491e2468cc0a6096f3271420d5a6a2700265207982184e3007583728e2edc022f03c429919c1667a672e0190d01cf81618c1cb285b930408f0b010260f02b9900873a5b4c088f40f9b5a21e25cfc26d0451438508509b4c060e882a0007f40673115f504cfe84495089a200ff0863d10040105e00000000000ab9509188184430a340005813cd8837a41b3d0139d032400002c030815d7c04c50003481d178a42425ec00001404bc2041e142a2247e502f00000916d1417a74adfa0571c0f33441d945ca70a4cfeac8211bbc57c082a4408c84013a812f203f4941a10218981191c326b11c902868c30b8138d6119ef4b7d42d7280c08c9af422c5036d807411eb13010e2453e000a028aee7d68e788402093e0459a0cc8c12231a8600001e1add45325845c70486c085bc2f82f358e86a3a12d54562803492282425014536dc13a1e1683c011642adf0a5aaeb2ca4f844466800006159960c7580792887f00000e04cd986c8000000001e1c9c4283d92bea05092a531c0e20162f728639c5e800006200b80f2f3d085cb1108857e14cde2d0382bf384e3826394443a84e9889cc313d0e299f4007b0a0a513f65c41f421af1a9ec0011e2de648a0d804f0000160635435d382f1f0fdb84666c084a84e6000008124 else (if i < 9 then 0x2e000000000000003926000000823b583f8f0809f33f4417d9c02a000002eab800000000078ae5000012db6dc336684410000000efd00c09136e000010250fc38b8000000000c2c0c45a60000043277914f8c5124204f215e121468c4bea047c436aa42adfc0f2188046152780bfe830f8000000000f0fea4092ab0b8d087f618e2cbb498a272334b681e2a3dac08f440912a0d4c404600000424ae6257a81753859160adc315058436584ba703e1a07fec5539824a90b85e5c084297f840732710e2a870374b801982054a49d68a16813ccf078dc12c461ab800007105b60ff1428ca85dc1098e01674406f800007032600003425a60aad4265a008eb089c404d3604d6c666388172849bb124668270032f800000000101f6082e3f813d030e342929022dbf10ad02230141103432870430efbc583c821408a33c30e14076cc130916992229561ef7830a98aec00106c1e483137f131600001227bec018e80d22122685d69e2bd80000b32c1815923acb800000000040a5503568000000000e25ec0000304b06102c00003802118a79c0df2a1a71808808173d101a80cac00003c35ce273f2147000003914f0000000001237e0000000001626e629d0d99e800000815f58349786840000000000000000000f0c4ea17e0000048324c0506603f9c35418b56000000000180d000000b0357c1294c3a4800008296500a3e69222911b0000020be305d0800006135526cfc00007819bb0d4241c5640f780000d02ff80ca00460413d0a06d9c065800003850ac32ee855560356787e1a037be0bbc4270f05e0429cfa1bc1cb7d9d45a0000060ef8000018994612a66459400000410b0000180f9c4a490000000000456f80000285b2f059cc164e039680000004e4c0adb0c4e80000529732493e8cdee02b2807d8c284cba9f8f598988f1a0c3a05027073742cc6a19c30a7f50856f083822d90000010336b15ef81bde84059952d10b24008854216f046a622f368265c16fa81c0fed6f2175b83c4d097c000008526f8c2cb99eba33fe207f643f380000c01cb41d5e80e5d04d6f055689f8770af5650ac0e51e2d4c44e3794807126c02dc00000686f1c60f5615b4826a498498055cc1d3cc3a5d057c40e1400a3a03fea0290f23eae0b9500f55806242238a105109e7189a822680e275780a6e10372290fa0b9c0b6d60837109a11d4eb03d000000f1737004fe4ce300000e13e92224a782990a462208c81496cb81f20e0210d6ac244430200000e0d918084a4d44c805e52cb7f1531c1a2d9b13615f20000083a17120a00f0d2089e84a138a08a124eddac048f1b056000000c122fc2a4a06772276c41396c3a93881b00e4ac0dad484736149404dba67160544a8394932f0111dec478701a4e0ae44666c81a7408a2e063d0287fcc8af0a5fb005341b86c4c else 0x62ba27f302f8a83770000000003cd10f8700441af2074e85970840f90cf800003ca1530ab2b07e1612cc811ca92e9c109440da00000519de7e2f2e805600599801400001c61ca807be09bef04e8c243ec3de707759412ac0c70c540499c3b086646d64c3dd701acce55061ed9c3ac08b8a50b4be16294b4a40b3100001e142c844aa0bab000000000000003886100000000000000000001148000001cb6e00000001ba05d06c4850000070e5d414818b5ca0a5e40083e011e984d0000000000000034b2c00000c2c76000000b6b603470000080f4cf9fc80000323f2000000000496a60000000003800f00000a174be81adc49c6818a015f4000038d210201f4e863e0d3c000000000de04c201da41a1874d8000008805340dde8b92205d7a832142ab6029ab021442aea019000000510f040c3470d70000000001452b8000030a9d30d78e24b68d4e80000d0746c41ec84d4b0387706a3e21c745708000000000021cac9d8a09f972dbb3208c62a3f871118a94c2c488056b11e800000fd3648320807a600000018364046f8680a0ab100c30040e6025100000a14c4709e00000000000000000004026f00001e05b603dc800000000060fe40000030afc11eb8241c0000000000000000003c847c1afe0000040b644426689f340a180000000007938f910db4167245bb79629c06df41e1e4414b876bb40138085645b6610b500000419f800006052740670000004add10a0dc099295f3c051ff8355433fb61a17cbbde87a86082562c6305be589331ca0822b29327e888b270d7d02c5901ce58197e8ae4e146f44c3b0103827748494ac3191447af221b60a9b428170648641604583b8b785a6da22c88c4c8400000000043562000000000016d974008c43440000086b3c1040e19d4856af876412e70417b54036d97f800d496075e00524053b41381a561622d011040a0178000018083b88428052e214ab89e6f99ce82f3582c6741e6985cb326286479083d578b1ea2ecc2c2d78367b003010e42fc1e18915a0a20016fd00b5553d288a72411d0e28b9cb32593c91e5867c4428360d8a224e09e6012e822f5007c9174c2293683ba00000d3085c28c00510d0538b0c1140bf0a2bf3857f000002277c43168828c8611344f54017f00b4d00001a186000005e1bd00001820bb457a000005013222d240000000001277d42e38000000000a0415e554581e580000c2ff6000014507787e951018c13560310e9b3e509c5c16a643a4383a6a14db80eae005bc0854000000000000000000000001a0b14000000000125b8000000b60800005157ee0bea84218000051696803e901c9189ebf001600001cb57f93d7714e00000101c5500c15405a00002c14e389d67061760875852a707dc0000140df400001803e70d880000342afb92635220c000000000701)) else (if i < 12 then (if i < 11 then 0x8e5b0317c0401240194583182bdb810ed0bc981ca6424bf63876085d9cb024dc598278513ffc0a7f82d65831b73734802bd78f2ae185708b2c2eb3427c587d7410801823b4d88905db8327d05d9400001036300001c061040d4085e65091f4286021b03899890187793fcc8ef206e2a0cc7e20948538f1296e073ee61dc451c08a7d030a38047400da2866a9137a41970088c7208aaeb35b8763c08f6950a4e226055518448888ee6048ea018d049ec841b622722290f8541c99c710bef2014000a1109770039502daa0539b8582107a83c2cb8c1a508fc1046f429b30b686860ae0a6ce07b462abc198c1617cc11be43efa85aae24cde034e4039c90156143bc04df820348481988d024a8501ed599c200af3a071e4399506c5304b240b60820648929607aa51f63c2b3212e0b15cec06bb889be8b87b031e20f8581275187fc2d4082016c0eee891cb3111600de05017a011e2a5424f594120884b2e15a96214c0ccc8524d7076888061c52c1734f1e6ab80a7909bb7847bf12e46009f0465a05bc9049ea19ba104f30adcb1140523b40dc4890eef0e1b24b784498987072311704441c4db99952027f6629aa40a0809215e21f620a9856c105503108fe109acda4604572114f01f1a88cba189c73076210e6043cc82adc09e3802c083cee816940a6962b99803420078b01533cd4f905998496c410982e71856180000c076fa13deb04d011dd00001a52100000183b8f4057826d6046ce01f4a130880170000020a761207d215df0029b00d500000221c04303508fe00001004c2c47fb82071ed7584eaefaaab80a5e01ce622374c1aaf000000005150c0000014b5505e600001808be18a2f03d2c532bc0382e41ee1534823dc4cf92808f91333212888594208aa51549e63dd432da80263e3a0c2bfa010080784d1025425a3cd7e100f38347a024fc0d3b30aa9702bcf16ac000008ae320bf461c2482a719104fc03b0271400000812c00001825d44dc7d0090c16b9e09f40000488a8d36cd4173649e5cc880b2d34c4ea441cd61ae5f019734beec3b0f08fa70b42a8200400ac091b86156e1f6dc9e06824cba74f7eba80000012dda1704c9b67c242514e360fa600d8b04b34056b40f932150c0000299aabeab640fab83ef1030f42132b8e65d84c6894e10fb5a5e67c5c628605c0b69001c78338e8348f16280029fa15e30557e154600000000008887c200e0000143d66826ab24dc1c0504c460184a412dce4ed683bb985df00dde2253d41ec70a8b5132302ba98971e8374ea281e2a39943c30474e107244d380042c16d1e0001c49268145e178f4047c000008cf350a3d0000081afc40ed48659e09bd24b948a277049862c497626d8442599021a76e00000000000000000008576d4d07f869410684a05c543a1985c5c0a3cc2b88000000000bc else 0x8aa6b131310553c582db082b776c9062922b64e35c108bac06cb8c22dca25c025340d68a0aa1ccaac03c7b0dc05d4e603329093ac106944f21c006710d890b2aa1df000a3f870fc309d80a8f094c10ab0e0cf1029ac0326301e8d02b1a186d9821d8089a0bf6c800800006a0c3e1334c00698bea80000e13f1c01fbc1f5f4588a0749e1b66c38da188006178c1693828e8075de2fb2e6894c423501ccf2fa3a4d9503078874db06b786835c22b605fd100804451881893962edc8af40552c0766846cf0e0de08bdca03102028327e74ba18407a86b128b073c5e10194f028590a85c58fe0ab0c0167a0bd9e5e7143b76883e71029213acc0225818540fa8e807284623d1326039b6415f41330f34ec0e1978fcdc5adf815560202e48b6c42e1038bb21df62b1e0c137013a100b70257c40bc78b3f1115fe0b86c08ad8657a11cb20d430568d083da09e60000141f899140709c07162f1035193d3725df22b0a03170000040ad0000004086480d4734d1016fb450b8000000001b8cffcb7c205126338961e170019413da8090451ae462ba8d4594093b2204180ce389d0000000626f43acd0093a4129803c7835128ab8c157d84973cae2e0b98c0f60a01934a44a8565501f861838817a2e93a7115b62dfe4210f03615ca17bc14aa2a46c551707db617e702f92842450f4381d4ec10c6f3ec70ae861c20013ab90b320f3541da8c9c5f896a8410aa2a2844cb516dbc36bd411c2c10770948c2873256f40000101b000001a1a81403628979f172e01bcf045b289cd90f62852c3827c881c6609a40000000005704e0000022077c2acc83a5313f5021a900d377177003cea4de00000389a7a06638589b41ec80000207ac00002c27e381b100000000004381d87d9d2c84c05ef1859804b914058e5ee00000087be50f8645cf4000000000a130d41307c0116a0d6e1612c8191c8e148129d401bf512bc3912a024f163e017a3859f409582071060a2901b7515b8607ed0266c00000000000001e0026b9ab2858db1100a07ef03a288a53d349ae014902fe383f7a0d8d8200242d5e86b9ec791a49d08b53e93ca204608531b8075e83fa90a2ca05b82194f9b4710c3d4c360027dac0d04022d205bd82e0b871a8167480a63029fa88219844244ab28364c8667023c2e240b40c8e19b731303856ddc2236831092d695eba722b1b97161113fe004cc3724074e9018e0431bc301414cd1040ae2b048836a8ac812b76406b6514d900ef14e456185a4b78889f7c08ffc2629023c0835202ca684e1e404d28b544166c86bf44588b833f60d9cc2b4904f2005a60054a604b444911043dd0dc62c2354228df0f42058842a6f9026889d1208f320c5dc23a9863e428a81c88c021b284e4304a00172585005880aa09214161a015f404fff113b4492bc51b3886900e049) else (if i < 13 then 0x607ae70d462098c451b9a0131205720d63855ea02c130759e2cbdc524800000000101c2e808e400d6d33d800000000000000d0da085af40000287b300000da93288988000000000c83274db1884bd11576000ecc1dda89f2000016021362d498ae040efe0128c445700000f33fce01d042cd997540000000001cb4980000f8ab44221b4353d858e90268402e000004123700000c193c839599a23f00cae2e3f821008626b1384e20ed0cd8d07500000000002428f804ad0000101f06c3ce0000000000000000000105bb0000021941f82be017213242c0bec00006f32900000e16dc00001812af0046000010178492c4402e9e08d800001860021490a2197c5b580286c03e58037bc99cc14b8e01b821b00c518905da22cb50129301c19839e84148a068b00fd3890c9013e85300cbcd9077930d3c409fc0005708d6fedfb9207b824778494010b4c1328000040644133340000044f7188dcd13122131181b9a27e0525d7e27c201005034cf1347a08f204641924c40cc1e58f6807c48956000000000102a3c122f341a320b3c4bba101000106ae27b400001824b726f3a2038000068935b211a84885c30eed84f0000046d63036bad2f662847e1d7dc019b989e000000000003e47869f0000100af24553682cbe1421202fa4af650603d2300c219ec2d87b08280a1a4150500d0f046b90a66e4d11c04368b811207042b7f41be507f60000100d19499f8058fee56dc19bf813b6814000ee7a25fc8174203ae7027d6204e8555d09f620503e1aec000070395a347c60e6dc3b7f95eff323604f4b834440581f20e1000af4bc6f8b7b215a1618534d3681723914e9e07e08590b857a6163a467424bfe4655d20f69a1766015aa0a2a2e4494033e0530283758054240980406670b5f5419da16f64915106ab3034b1c42681cb703bd10aaa408af83aa30a550310540d9880fc9068b40f27461984341e865d2e56f014628cc0b83c8f165554e6644046e44470f8f825f9f093013c72c7953014af1c6b011bf0e467c878d0306021122c59c670000004101e009d400002c1f7f056900001017300000000001a37b42549c312093d800b9181419ca4e01775916df91adc00000867f0356680aea82cb3104b00001c4e74e8c2e9425508fc00000000060a3ec047104deb8c89a8313e164e259f34cb62cae7023ce40131cb0c00000000000000342ea109ddb10faf178800005036a0000181f2c0bc5b09b3f13ae42ce7cc8a68b353275922acc0000788180000102c8000004101b00000c07db452778772a0e0b600e7405db863620d316044b42299814a8ea7a24ff6880e88004b046a827230264109a2600544c1122c9320993632dca15440b72b894d2037d1034984b0b0a5090977407f381c79192d0102a22e8a4b1f1073010c73c1a65c47089817c2ba962a59 else 0x3183e9823fa06bc2826d0c750124040c520194f01c670553325dae136480b86a06cc0f5a422df03455006fb0074e02eac0dfa03d161170c07ba84581827ee05d3021ed839a08b2b10b0e20b3303c8209e11403485acb8104703c0d2debc1b2fc4e1b8322a23c42148f02a44155e125d1a66bd0b2a701b7c05c9609c702578909a716360012001aa3998ff0e7fe1c79dc3f813a090ef08287170a6e003580277604e184aea0454e12ae0087d10608000093062a0e17024e499e53019301dfac34de0194c15ba189b844d0c03e5501228015e8425f06bd308c142678424fa0925a4143c1e3889c350b2d8144a208b5c255b02807368c0000162cc0013581684e2ea6cc36883de310bc00001c4a5008ac82475a26cbc46d80b6d8033fa28eb455770400e61dd81b78c994))))
def p3853r11 (i : Nat) : Nat := (if i < 1 then 0x1a5451c746c73f35b332b323a120a01a8e0f000133768282563239f9ad9995991d090500d47078000a199471d1b18f8d2c8cc8e8482806a383c00048a38e8d8c847f6665655c5c454040351c1e0002651c746c73f35b332b2af23a120a09a1a168e0f0001528e3a39f9ad99991d0900d4707800079571918d6c8c88e80805e3838037eca0978c7c6b6447431c08018d1c6c635b2b223a0a18e8e0c840200fe3a3631fd999591513121150100ac7874706028000a93f1d1b1cfcd6cccacc8e84828058563c3a38301400059a1978e8d8e7c736665655d544f424141352c2c271e1d1c1411080a0003ad0504fc746c73f35b332b323a120a01a128e0e0c050001768e3a3639fd99959d09050c7874706050442028000af18fec88a80863c3a3802b8d8c7f656741402f1e1d1c019c746c635b332b22c23a120a0178f0e8e0a02013e31ad911d04d4bc7004f1b18fecace828042383802ca38e8c6b66644742403428211c1c1404023c6c63fb2b3a0a18f0e8e0400ce3a3631ad9995911d09050c7874706040201009b432f18d6c88e863a1002b8d8c6b6565431d1c013c63eb222a18f0e8e009e3d91150c787473f1b18d6cac88e82863a3802f8d8c7f65655d574141352c2f1d1c01ff7c6c7b2b3a0a18f0e8e00bfb7a77736ae363d9595755d0504d4bc78747009f1b18d2ce82863c3a3802b8d8f65655d5445431e1d1c019f7c7b3a18f0e8e7fbe363d9595755d0504d4bc78747007f1b18d6cac88e82823802b8d8f656741411c1c012d0c7b2b3a0a08e0e009e3631a59d0504707004f1b1ecacab88a82383802b8d8f65655f4141351c1c017c7b3a08e0e5e3631ad95911d050c747005b432f1b18fecace82863a3a101003b8d8f656445431e1d1c015f7c6c7b2b3a0a18f0e8e00bfb6865e363d9595755d0504d4bc74742020093471b1ecace8282383802bef8f67431e1d1cff6d0cbc6c7b2b3a0a18e8e840400edcbecab57ba50ce9e4db0937b4b87d94abcb548a51d03a6e32c4923c76a2eb0f8825be59d52dec69fb3a990abe85cdacf9562a4c4d7a56921a8c0441a098f5274c3579968bea5b829d939893244c1ff8ea869a32016189383f219c08382c80ea000bfd84803ef91200bfd83802ff20e00ffc83803ff5ce00ffc73803ff54e00ffd43803ff8ce00bfd82803ff5ca00ffd62803ff54a00ffd42803ff4ca00fee22802ff60600bfc81803ff20600ffd41803ff4c600ffc31803ff48600ffe11803fe50200ff930803ff4c200ff830803fe48200ffd20803fe44200ffd10803fe04200ff984803fe55200fba44803fe60e00ff883803fe5ce00ff873803fe54e00ff943803f68ce00ffa33803fe60a00ff972803fe58a00ff952803fe50a00ff932803fa88a00ff981803fe20600ff941803fe4c600ff831803fe48600ff211803fe84600 else 0x2ae3231ad919500bc7070200671d18feccc8a88a80863c3c00034ab8c8c6b64644740431c1c0801bf7c635b22a23a01a178e0e0400de3631ad95911d0504d4bc74705010079571d1b1cfcd6cccacc8e8482805e3c3a3c0004de9dcd1cda8ab8e8d8e7e6b6665655c595647424141352c2f1e1d1e0003a67c746c63e34b23323a120a0178f0e8f00012e3a363211fd999595755151150100bc787478000a71d1b1cfcd6cccacab8b2ac8e8482826a585e3c3a3c0005cab8c8c6b64644740402d1c080)
def l3853r11 : Packing := (60,2,6,0,0,13,0,p3853r11)
def p3853i11 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0xc40ae4c063f4485232ea4876aa560000000000624db08c50a6ac11c00000910f8e28620cb8427910aac814c623ff436562698c298804ba4bdc307ffc34561316827608f73c30aa2ca83a5bbe4a2c32a029eb408bc05785025304eaca6f60c51c3815e6050a9a40fc7c07280620000040f2a0042d4afc825ea0645d81350c9c4b2e1008ac91ca245ec230c209e4a63d0bd4c2e9d057181acc0e2b0083403a70492001d80097b2a9881557124d0ae9a28974a1322e3a496872f1d8064211c400a9b01a901177004d8416e095b036ab02df0865b047781cb8007683eb61145847de2f2c009470c1b4198022878acc32402783860e73c0beb2f6a000952d164453000000000f80e549769000f4bdbc05f8449134404ca8f34061c15082cfc44801123bca8b10f5e8be30000304111609ccbb00000081862e773023f9102681a5f2ebc000010e9400000000061d8000008c6b000038c57827f9c24870ff3c164e221602ce08000000021f09150008010030001f41072803010009000105052233032c0002000321251d06020403000101160b0431010a0a170306002406100e04000a0300001e03130c03020012080f590a030f1e1208040d0c000310010c2d020d1400000a2000000001040415110d131e510d00010603111100150003032402060900151f1b1b00030b00010100291116000401000402022a13047614030900030305000002012d0c06001f03020200050016110106003b151161001b13005307210100010002022b10003502000a2502160522000d110002020a05050700065e01012700000007000702000808110802000030010035050f000001006f00030306000c001d246407080c4d00010e09003d08000100000129091222000d03160b003d01103a050c070a00730a09060c0a0004040415000a012917020700000b1b0703250c000d0c00120e0134091504144b00110f01001702101e0001041037051500000e000f010018050b001da80000040701048011011b022e0a020302000c000b0207050013050611080308040e0d073000320107150a0306060036010f0009151100080a1608100d0a540d060609000e0415000512030350000b0b03001e000768090307001b000000141a101203010c020000061e000e0013024a0110002c010e00100207000f0304010b14002f110001011c0f000908160004060302000b09001900070000041a0106050204070213400f1903270f0b010b0d040f0d08021f18010f06062705030c0403130000162f0a01012505141b070001190f040d00020240173f140002221e031e1f050d2b070000000a001804002f0a0538a60105040d1002010b3a00090a0e1d01006e00030c02030b1c010800090010010a0103013403350000000a004e0114021902070916010f2100130203041a0102000003 else (if i < 2 then 0xcc9275840a6529b0810d02385092be10d1c3d810e4d444d12669445e005c6c834201e182032125a02c39116cc0fa410e1c916d2fd1f13d940418ca1b0083834aa2ec8440ac0dea0181611cf81f17245421c3b0f7f48f0208b040bfc0699001c30e11000c4a3964ccc004c0c2e39e42e8257b086c04b99286638118923442bd7247803c4b0d57827d78cb0cbae8ab9142a03c6ae42e1c32d28288727a24905f203bc1619409a483e222e609eec308a6c88606f0e1cb4002b44a0e006808210071f0271a0ce4c25530924c14fb260003bad050e044aa2b8580c5730528200c073c826db12de00aba09fe4c05b2a32c9ae90204b9c612d824bea909d7c0b5c091842f15878303167018e02d7c0362c0caa0c0e3433506d8c4355022944e3521ce0402410570a65329c1c487c000993341307b42afe0fd8447b621f80000629f00000c01370b5203261c334a299ecc072261c48d3f100cc195621e40449d403e8aa542cec82f6712ca4a14212b983523127b002f5080a8959400e603400036b4b5ac0826c2479130389e9000038084d0d6b08db4013c0000f2ff41b40729edc3056077d830c80acc0b37806b703ac7073043c8000000a7862d70024b000030245601f0000092f8348e610fa3892062b1c000090a2c425b00000000070b1c00006031184dc000000000e130ac010c4cd50079905a80000c08d80000f40b9c86d203cb017c400160846131a9c13881295429218f88c92f7216df86be069d8a1a7122740ec829a7c1de22a3a839150dd8821a408f04a740110cc8dc324ba495370582420180ec94ca3f0e16049ca09370205203c160119089d838630230403480f6bc20710b13032602f88c03a304e6412bb12400000b001a4c0f5054909b8549540000c208b029c821140000d0a5a00a210b240000f11ac00002077440a480b70000092b8ecb3c9041c802c011e942e71400a809112bed017b8015fc2a2f05b800000000142d0821494c21e2d27422382c1784da62df98a9130c27040e00befc452e08314bebb0fc048005e7794817b07e28a35b07245b3fb02db00db40aec389eb1323c13740a0101444060e0442a2dfc80d0725c5580d60ae1cc23a2d7fc33ba4067c8b2e013b01fc908370b6164ce802d5d1327021740e820116a0bc8c8844e345c9ac506328b446406d09d0731644ad820321030f92afc083500562048100001835d822000000000020430712130266f1312435be22acc07d000000000d0b354121530bf4b39f0d2fd01e5101d4270c044240f5203b483d200003839d702e00000b305c035c4050a4119f1306893d50e5801c5a0affc8b500001ca52113280000000038157f0771428c000010370c0505436390f00009002d5601e190af00000b0a240000f21574a9600e348c53309a24237b3170000002078836710091e490506 else 0x1f34bcf60c8400003008f419b7872bcc040064dc10a304fa23c902e19cbb14023a4070a0f0dc382c0f1461c26027e0156607c84120c030443e252c940000000020b630000104a2000000000b23d9c19dc20b6041c8037240add01dd4abe4304fc1e82025b033c60a120a7310828c809a2575c94c00002c0bbe0c1021c65040ac27b904d803c2305dfc21ca1106c0d4903f100cd70cc8c29340394c9a7221cb4482b0cce841092959ccbd90178c3d94117e0439923680239707489828b08c8c173c204cc4bde223b403fb010d0347410764b517044c89a2525ab88f2306808185000000ab3203e4c8e40877713334094a43a2b10780000d1298d015b200400000000000000016800000000088713256a00e8102c8c4df9086404443043c000090d7cc8c82292301af4082384c782dd489c692d6fc4b0a0387c31f221ff03b46050284ac33001489190a6fc233908488cc9108aa0082a07570154d0f3c42dd820f642a726c80789d0106c133b30f274a66c127d030df23f883a47a6ed0b6ec229081abf09cc8add30ed7c01f70132c2d8925457b460074684b1b09ac0000c01970ab290fea2aba51152c2a85e343ca7d628980000f10c640f450b2b89d530110443390cb7cbab90f868864304958105c04f1c0fd429df4192c0218000030ac9b1206121bf9d3f0bb6b9bee286343f500003806f5109a83dc40e0c000000c6a822262e29427e3038c0000000010bb800000c1ba000038a23bad7b0be902ecdc00400002019cf10ca022bf0ab05b3a1896e8218a23e28a71b0e484394a01b40000000008c88a0ff4000030f5a4bb5123bf84e0b027149a96032d8311a135c0000f0da40000000000000922080000000010197000000b5e20a2a8b7dc135880559022743e40000049f90000000005295dcc77000007949a0764825f260320911911650170310bb82ffe087a0169b0977982190b65013b70b8909cfe0e400c06f202ac8aae0aeb82dae29258036dc20809ad00de68ad9f30694015308b4418b2070fc1a4d10944175404bc40c03078304d5b1190ca64f83dacbfb729e7894810794439a2404b0401b046f0a89a30fe021650fec420be32ddf2ba8010044235132d40cf4093f00aab22d8c10cd0cfe1b39b22a54463326dc705670db44397d0c000000d209303737035e085000003846a90cd680250028c0000a20a803bb4200d027a100adc9065031d003c5250b444e12e854c0310df40000626940000c0ad4000020ceac06142d634a11b0bbe92e9708a64098f0634f9bd504ccc3ec02f9e83efa102242f9d1228c457b11d800003e7674bb7010f402a4e2c4661c100001c4de2049a40ba0000180e290ee68b10d052c0000d047340afc03574b95c08f88a4b20c60c08fa012a8351a08bb04b8f2ee6806bf27b14458324f179bfb25d3c4977048ac0)) else (if i < 4 then 0x958000000000d0c92080400001040bb2db402d6620a680127332a00df90aa9c4246002c80d1e2a904103909de02be300e103502057683db80f834420502e784652026f438b0000000003228a8008b0f43c1bea090e8abbff22e414a8076e8b0a72b0f01f0f20580000f32eec4c6b12ef810e607ce44cff05a04acb50728c12c001d682e5a0bdfc94fa2a6c48f7d0c3a4092000007c8df0a87c9a1b03fc0000107d2cb14b0dd7c12a20b20000000000c2fdc00ba43a7b29680368329ae40f6511a7426370f1a8b8890aa7c11882798000052076a85622f6001c600000c341000000000f031a838e30d78000000000000023283ccc75efc7c27c8209a425392fda831c107dbc40641392c0a7b0f9bc2df000000000f2158c1a8e2a5c0000b8fb80b3690c6d01d400001c0a1d03814019d01604c7c60cf9441ff0a384bed429310147011d6444020ef0b17438a84000003259cb3a02ac40000000020a5f000000000f30b303ffd062504d25104d00d9c2eaa8282212be01064873d5ae95100180e610bad84620000102b0b0bf0b055331f50969e29c80000106104ac2b407188c7803dc8af10000000000000100f1d0e3e84d12405361d2f07994934403aa81c84058f43aac2ed2493550d270b046309a4100d235748fb50ca18074b0536884ce32d5406c731d8045d127118417701438b8081333036c42cc082c092d66b159a31638041f0659c060132e1c30710a1d89ab000010a244049c00000068c0095000018389a0e6d806642262b0b9e2134000010e8f424170f46c8a300000000000003898ac04480000704d40000b134f43cc31030000000000c3f2640b7c49852f4c4bd0325ea0b18b07ed4a15e0ebbc165411848c6cf058809ccf04a043105218e0bfa43080c37fe06f58312a00c00a6e0000083a600001c1da000030380f85268a28c09870c4641132ead1d13774477709028b19e2f644414b05226c33c136d821d40f78c238a32f2849aa26ed4338611e20405406e54336b0ba8c2d1000027810629f968e40608861d9530420c02c0c890989c2bc1c4a8000020c9570a06002ae2c3f00c2902bbc0b1d0c23c03b32ed844a3e109ec35480a0c029fc321c004870844000060cae4983903af425af4d01811ab2c9841fd00ecc8114192270c52027e363f1a2d2d828590eaf044bd0ae44032321b8080c72440c2583e716c2a370f0403607027a825c52cb40000d0f378166701a283875283c000010668e23f0000301fa3039d423a010eb4811d2d015291400508146c23888ce0ce7100a5162de881b27200949554119c0251612930428c0a3f0317312b44b1360d634357305db04beb2a218a47b255c8bcae0743c1ec50b2ecb89de70104ba58740c24ed12a84087e0171d02200b4a00691206ec17852017445c72e10000010f3a0a600000049d191 else (if i < 5 then 0x1c92af296e0a4d0240a8a5300000000000003023be0c64c93ee2f30845560be34199510f1804932b464810d07ae8c1972c57042f320a004946306302de53103083c503758374f0d3880ee203ecc31d80d67d003011a34ae0c2941440dbc561a1b6f00cd4cc8f60bac115a04a4ba4d7aa384398821e34007b04c7cb57000000000440a30ba390891c36f52e6d08776047e093af206743ea605b0d8262248e7c8eb2d5a036b000000000e06e00000e0bb2c29540a740372d0c06c42290a9b400fc23c7cc5bf005c000043129001e8215d8cb9401500000d08814988f2bc8000012964216440085814e924cc000000000000020280000000003042c010ef4853302b1c05270bfa00fe00c78c0930000141b3f122ec80d81064c94dd00f8829af089b43f7c0b50441a712fc2b3200000000040ef762df0000080670000041c200390000000000c3b800003210c211b082cf30adf8088d2b5d80b3d020381d73016c098200ec343bea2928c2f48a56683ad00d22c975f0fe20b278138941ce706a44329812d6cc78002978b17201c481cdf07104b3880a5f884b408868c54880ab0a01f0c4cf9d8a40004c9f70ffa819e42dda43b1b30d20bf5411fd84d9222e80b31c12a683e58ac5dc8f5e00a0182d20d0f44a1c0687828d80dc5c167632cf4037b0007b1d4d2f46c27430fe5433d2042e0a5470950c42b9133b89c5d0b90a48c02226016b5409d407b9841e432300001c1fe000000000e0fb5d26184028000072fa0c483b2f0d01322042480d300003090326cd5100b5009b044820e31036ef0d9141e3f8d18019fc30c99a91c2ab87bc982a0c000053169c1821119a805fc08d048b16f230c85840896248e405fe4018c09a7846df0f9f0a5e41084c159523350099e24fc48362101308d410c2c000060dddf839100b40000b23d248f3f0701426fc011400006009fc1b030e65c39f00002c1e9811be032c0000348b0d2ad9e0d1a06d2c488e2484046e013418a9090f5084abe0dfacc36f079f0986e05bf0123320ddc05302665cb32f084104473204bc20f18714813450f1c8be4705457994c0983c2e0c0f2f03b7830bac823a0de28366000000000000035339000010bd20030d409ab0044cb790000140004111444d830653812dc0d3e80b042cd4c22f331cf426e411c8898c02b3481e20000004958921400009285c8145000000000a8711c2c53115b8450ce75dd021000010031e0d100000e0d30c3dd90643413d40fd0c264140158c41a01640000d05d2e1cea2f3980a8d11f9005d0000182d310b18cb850000284b6d272e84bc0057ee48bd06bb4c7a3e9ca438821334000000d3481bf000000000c6afc0000d2e90000042a62cc86000024302406d4000000a500000c2637491b00002420680d58f28e30216491a00003cbee000024b4aa037a4 else 0x1101a0000004b310e54c418b22ef41b7d6ced1b360000004b4606ec00000000202a5000024172e0b33c412926e848afc875101a230ea341ef00cc1932090bb942358011808b74af4b80c992ab49004306380000305f7c124d0b0a8aefd0c800000700a610090000341ead034909fa709328073f113e026c50159436152f7f003db0d8b82158003502ad7062a08b4b0ebfc035c2c80407e310a4c818e1118c8e5728a78259a118284a700000c90a7e432c90f82c1b842a31235c3a900fb9809d00bce026af023471ace0f4c44379054c0000b07e541c1a2ffa404b10c55893612bcec242a877248fc7074e8a10ecd784149e2ffc21deb0a6403e3403e04262d3175c33750ac443e90000380bdf0941817a292294930310db02280280e4ab7e0ded001662606d336a30cdc24a9084cc39e804fe400ef2a1ce1cc7248940ef0099642e860bc0000000000000000002c84e1056c048c40d19811e00003091fb0146842d811d10ba222ad40000120bb89f1f06a841edc044583b650911c21fa211ec2db71264829e010fd848f501884108909e24290a241c437c00a19420e02b970acea041141012203c4a990000000bcc2b890047ce7740000e237400002237841f7b2147817900002a1d7f0fccc2140000384d4e2069089200000040f000000000932500000e202c00000000002ae2332f018700003e2e8d246462722126dc8fd8099f0331f033bc27220cbd02b4c130dc2b621275c1e4a006d0479907b80000622f00000408f5633c50568000042b100000a0b98000064cfc00006400581f580e86c4e140efd820400003c998f07610291000000aba9220c000080d4ec0d6000000000000004b2f00000000000000000000003816df0759cb09d01fc000050b0580f300000000060be8000010f5580b4000004325301bb4180000000000e116a007a80d0800000000000000)))
def p3853r12 (i : Nat) : Nat := 0x31a33e6ac9923408470e019ef1d9a11c39af03ff007fa00
def l3853r12 : Packing := (2,1,6,0,0,6,0,p3853r12)
def p3853i12 (i : Nat) : Nat := 0x12929b000063100000010c20000000000000000003000000164f8e780000000000006964039267f134111c0e00041938ae0baa36000000005e000b25c9e4001a0e838b9464e000000030df067c05f3210b800000000000010f00000000003821a0121d919400022d9098002c040000000000000000c36995800000022700000000000000000000000000000081a00053d008f8aa22c00000034e8000c0c80008420000307048831403a0f000305000000039c80000000000000000000c0d8000000866000197d82e000a2400000000000000001cdc000b1c80028926730000000000000000509c47000000000000000000006940000000a87ca00000000e22a01146a000712483f011a5ea0a0000000a0c50b00000000000000000001c4d0000002c2a211e182109c16000a3b80000000000000000000000e100001c87434605309583a0003310000000e29f110928001c1a000000000000043d800103e00021d68a98d6000000515d000000604800200020040400008000401080000004a09c0000000
def l3853 : Nat → Packing
  | 6 => l3853r6
  | 7 => l3853r7
  | 8 => l3853r8
  | 9 => l3853r9
  | 10 => l3853r10
  | 11 => l3853r11
  | 12 => l3853r12
  | _ => emptyPacking
def i3853 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 p3853i7
  | 8 => lookupWord 8 31 4 10 5 1 p3853i8
  | 9 => lookupWord 275 939 8 17 10 3 p3853i9
  | 10 => lookupWord 1482 5028 9 19 12 3 p3853i10
  | 11 => lookupWord 670 2281 8 18 11 3 p3853i11
  | 12 => lookupWord 35 227 5 13 6 3 p3853i12
  | _ => fun _ => none
def g3853 : Forest := ⟨383,13,g383.samples,.fork 59 g383columns (.leaf [(0,0,383,0,13)]),g383autos,l3853,i3853⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geometry3853 : graphValid g3853 (boundsBefore known383) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=3)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
def offered3853 := vars 383 ++ [minus3853]
def alt3853 := vars 382 ++ [minus3853]
def ord3853 : List (Fin 9) := [1,2,3,4,5,6,8]

theorem required3853 {k t S} (run : Live (graphGoal 383) k t S)
    (sub : ∀ w ∈ S, w ∈ offered3853) : ∀ w ∈ vars 382, w ∈ S := by
  have data : ∀ i ∈ ord3853,
      (bit (absentRow i) (graphGoal 383) != bit (presentRow i) (graphGoal 383)) &&
      (offered3853.all fun w => w == primary3853 i.val ||
        bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel
  have ord : vars 382 = ord3853.map (fun i => primary3853 i.val) := by decide +kernel
  intro w hw
  rw [ord] at hw
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
  have dat := data i hi
  simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at dat
  exact raw_required run offered3853 _ sub _ _ dat.1
    (fun u hu hn => (dat.2 u hu).resolve_left hn)

theorem fullLower3853 (tables3853 : checkedTables g3853 12) : Lower offered3853 (graphGoal 383) 13 := by
  intro p bank reach target
  by_contra! bad
  have pro : proper (graphGoal 383) := by unfold proper; decide +kernel
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pro reach target
  have small : k ≤ 12 := by omega
  have all := required3853 run sub
  have raw : vars 383 = plus3853 :: vars 382 := by decide +kernel
  by_cases negIn : minus3853 ∈ S
  · by_cases posIn : plus3853 ∈ S
    · have eq : S = offered3853.toFinset := by
        ext w
        simp only [List.mem_toFinset]
        refine ⟨sub w, ?_⟩
        rw [offered3853,raw]
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
        rintro ((rfl|h)|rfl)
        · exact posIn
        · exact all _ h
        · exact negIn
      rw [eq] at run
      exact root_index (g:=g3853) (before_sound known383 valid383) geometry3853
        tables3853 (k:=12) (by decide) (i:=1) (ws:=offered3853) (by decide +kernel) k t small run
    · have eq : S = alt3853.toFinset := by
        ext w
        simp only [alt3853,List.mem_toFinset,List.mem_append,List.mem_singleton]
        constructor
        · intro h
          have d := sub w h
          simp only [offered3853,raw,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at d
          rcases d with (rfl|hv)|rfl
          · exact False.elim (posIn h)
          · exact Or.inl hv
          · exact Or.inr rfl
        · rintro (h|rfl)
          · exact all _ h
          · exact negIn
      rw [eq] at run
      exact root_index (g:=g3853) (before_sound known383 valid383) geometry3853
        tables3853 (k:=12) (by decide) (i:=0) (ws:=alt3853) (by decide +kernel) k t small run
  · have sl : Slice (vars 383) (graphGoal 383) one 13 :=
      slice_correct (ms:=[]) (base:=vars 383) (G:=graphGoal 383) (by decide +kernel)
        rfl pro (lower3853 383 13 (by decide +kernel))
    apply useSlice3853 run sl _ (by omega)
    intro w hw
    have rawIn := sub w hw
    simp only [offered3853,List.mem_append,List.mem_singleton] at rawIn
    have mem := rawIn.resolve_right (fun e => negIn (e ▸ hw))
    have hv : (vars 383).all (availableB one (vars 383)) = true := by decide +kernel
    exact List.all_eq_true.mp hv w mem

theorem fourLower3853 : Lower all3853 (graphGoal 495) 13 := by
  intro p bank reach target
  by_contra! bad
  have pro : proper (graphGoal 495) := by unfold proper; decide +kernel
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pro reach target
  have package : all3853.all (fun w => (bank3853 0).contains w) = true := by decide +kernel
  apply eliminate3853 0 run (by omega)
  intro w hw
  simpa only [List.contains_eq_mem,decide_eq_true_eq] using List.all_eq_true.mp package w (sub w hw)

def public3853 (a b : Fin 9) := inputs ++ [minus3853, bin true (primary3853 a.val) (primary3853 b.val)]
def permSix3853 : List Move := [81,130,118].map swapRows ++ fixRows 64 0

theorem slices3853 (tables3853 : checkedTables g3853 12) (a b : Fin 9) (ha : a=4 ∨ a=6) :
    Slice (public3853 a b) graph (subcube (1 <<< a.val) 0) 13 := by
  rcases ha with rfl|rfl
  · have cert : ∀ b : Fin 9, checkMap (fixRows 16 0) (public3853 4 b) graph all3853 (graphGoal 495)=true := by decide +kernel
    exact slice_correct (cert b) (by decide +kernel) (by unfold proper; decide +kernel) fourLower3853
  · have cert : ∀ b : Fin 9, checkMap permSix3853 (public3853 6 b) graph offered3853 (graphGoal 383)=true := by decide +kernel
    exact slice_correct (cert b) (by decide +kernel) (by unfold proper; decide +kernel) (fullLower3853 tables3853)

def legal3853 (a b : Fin 9) := a=4 ∧ b ∈ [1,2,3,6] ∨ a=6 ∧ b ∈ [1,2,3,5,7,8]
def witness3853 (a b : Fin 9) : Nat :=
  if a=4 then (if b=1 then 10 else if b=2 then 5 else if b=3 then 8 else 65)
  else (if b=1 then 2 else if b=2 then 260 else if b=3 then 10 else if b=5 then 34 else if b=7 then 130 else 256)
def wr3853 (a b : Fin 9) : Row := Fin.ofNat 512 (witness3853 a b)
def ws3853 (a b : Fin 9) : Row := Fin.ofNat 512 (witness3853 a b ||| (1 <<< a.val))

theorem end3853 (tables3853 : checkedTables g3853 12) (a b : Fin 9) (hab : legal3853 a b) (C : Circuit)
    (hf : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size ≤ 13)
    (corr : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0,x a || x b]) = edge x) : False := by
  have vals : ∀ r : Row, (public3853 a b).map (bit r) =
      List.ofFn (sample r) ++ [!(sample r 0),sample r a || sample r b] := by
    intro r
    rw [sampled]
    simp [public3853,minus3853,plus3853,primary3853,bit_neg,bit_bin,sample]
  have eq : (execute C.gates (public3853 a b)).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute C.gates (public3853 a b)).getD C.output zero) = bit r graph
    rw [←b_read,execute_bits _ _ _ (fun g hg => (hf g hg).1),vals,edge_table]
    exact corr (sample r)
  have hout := get_rep (execute C.gates (public3853 a b)) C.output
  rw [eq] at hout
  obtain ⟨k,t,S,hk,run,sub⟩ := extract C.gates _ hf graph_proper (hout.resolve_right (fun n => n graph_proper))
  have ha : a=4 ∨ a=6 := hab.imp And.left And.left
  have tests : ∀ a b : Fin 9, legal3853 a b →
      (bit (wr3853 a b) graph != bit (ws3853 a b) graph) &&
      ((public3853 a b).all fun w => w == primary3853 a.val ||
        bit (wr3853 a b) w == bit (ws3853 a b) w) = true := by
    unfold legal3853; decide +kernel
  have dat := tests a b hab
  simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at dat
  have liveA := raw_required run _ (primary3853 a.val) sub _ _ dat.1
    (fun u hu hn => (dat.2 u hu).resolve_left hn)
  have avail : ∀ a b : Fin 9, (public3853 a b).all
      (availableB (subcube (1 <<< a.val) 0) (public3853 a b)) = true := by decide +kernel
  apply useSlice3853 run (slices3853 tables3853 a b ha) (fun w hw => List.all_eq_true.mp (avail a b) w (sub w hw))
  have hz : ∀ a : Fin 9, isMaskedConstant (subcube (1 <<< a.val) 0) (primary3853 a.val) = true := by decide +kernel
  have hp : 0 < S.toList.countP (isMaskedConstant (subcube (1 <<< a.val) 0)) :=
    List.countP_pos_iff.mpr ⟨_,by simpa using liveA,hz a⟩
  have := hk.trans hs
  omega

end PEqualNP.Outside.L_meta_3853

theorem PEqualNP.Outside.L_meta_3853 (tab : PEqualNP.Outside.L_meta_3853.checkedTables PEqualNP.Outside.L_meta_3853.g3853 12) : ∀ (x1 x2 : Fin (9 : ℕ)),   x1 = (4 : Fin (9 : ℕ)) ∧ x2 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))] ∨ x1 = (6 : Fin (9 : ℕ)) ∧ x2 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))] →     ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x4 →         x4.size ≤ (13 : ℕ) →           have x7 : (Fin (9 : ℕ) → Bool) → Bool → Bool → Bool := fun (x7 : Fin (9 : ℕ) → Bool) (x8 x9 : Bool) => x4.eval (List.ofFn x7 ++ [x8, x9]);           have x8 : (Fin (9 : ℕ) → Bool) → Bool := fun (x8 : Fin (9 : ℕ) → Bool) => x8 x1 || x8 x2;           (∀ x9 ∈ [x1, x2], ∃ (x11 : Fin (9 : ℕ) → Bool), x11 x9 = Bool.false ∧ x8 x11 = Bool.true ∧ x7 x11 (!x11 (0 : Fin (9 : ℕ))) Bool.false ≠ x7 x11 (!x11 (0 : Fin (9 : ℕ))) Bool.true) → (∃ (x10 : Fin (9 : ℕ) → Bool), x10 (0 : Fin (9 : ℕ)) = Bool.false ∧ x7 x10 Bool.false (x8 x10) ≠ x7 x10 Bool.true (x8 x10)) → ∃ (x11 : Fin (9 : ℕ) → Bool), x7 x11 (!x11 (0 : Fin (9 : ℕ))) (x8 x11) ≠ (x11 (0 : Fin (9 : ℕ)) && x11 (1 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (2 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (3 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (4 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)) && x11 (0 : Fin (9 : ℕ)) || x11 (0 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (6 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (5 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (6 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (8 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ))) := by
  intro a b hab C hf hs _ _ _ _
  by_contra! h
  exact PEqualNP.Outside.L_meta_3853.end3853 tab a b hab C hf hs h

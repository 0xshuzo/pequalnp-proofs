import PEqualNP.Defs

-- The Live/Run/Forest checker derives from PressF10, pequalnp-proofs PR 4332,
-- and its extension in L_meta_3853, licensed under Apache-2.0.
namespace PEqualNP.Outside.L_meta_9409
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
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
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
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 4 &&& x 8)
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


abbrev Bits := BitVec 512
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 512 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 512 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 512 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 512 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 512 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 512 → Row) (d : Bool) (a b : Sig) :
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

def asRow (cols : Nat → Bits) (i : Fin 512) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 512) (j : Fin 9) :
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
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 4 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 512) (j : Fin 9) :
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
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 512) :
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
    if (rs ||| column d z.2) != BitVec.allOnes 512 then true else
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
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 512 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 512) = false := by simp [sep]
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

abbrev ExtraFactory := Nat → Nat → List Decor → Nat → Nat → Option BoundPool
def noFactory : ExtraFactory := fun _ _ _ _ _ => none
def FactorySound (m : Nat) (f : ExtraFactory) := ∀ ops d bank idx paid c,
  f ops d bank idx paid = some c → ValidPool (vars m) (chartGoal m) c
theorem noFactorySound (m : Nat) : FactorySound m noFactory := by
  intro ops d bank idx paid c h
  contradiction

structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)
  bonus : ExtraFactory
  safe : FactorySound mask bonus

def wiresOf (g : Forest) :=
  rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a :=
  raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) := liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 512) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val :=
  bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 512) (hq : chartSamples m q = 0) :
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
  match g.bonus ops d bank idx paid with
  | some c => some c
  | none => (g.cols.read idx).bind fun ci =>
      materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases eb : g.bonus ops depth bank i paid with
  | some c' =>
    rw [eb] at h
    cases h
    exact g.safe _ _ _ _ _ _ eb
  | none =>
      rw [eb] at h
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
  []
def ifUseful3853 {α} (flag : Bool) (xs : List α) : List α :=
  if flag then xs else []
theorem ifUseful3853_mem {α} {flag : Bool} {x : α} {xs : List α} :
    x ∈ ifUseful3853 flag xs → x ∈ xs := by
  cases flag <;> simp [ifUseful3853]

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
  let ls := fun tag => ifUseful3853 (iw != 63 || nl != 0)
    (((g.index k tag).bind (linkedSet g (k-1))).toList ++ (extra3853 g k tag).filterMap (linkedSet g (k-1)))
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
    rcases List.mem_append.mp (ifUseful3853_mem hx) with h | h
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 512) &&
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
def lanePlace (v : Nat) (upper : Nat) := 2^513*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^513 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<513 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<513 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<513 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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

def fullMarks (r packed : Nat) := ((packed+r) >>> 512) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (513*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^513)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 513*(i+1)-513=513*i := by omega
      have ge : ¬513*(i+1)<513 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 512 = (a==BitVec.allOnes 512) := by
  by_cases h : a=BitVec.allOnes 512
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^512-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^512 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (513*i) =
      (f xs[i]==BitVec.allOnes 512) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^513*u+x+(2^513*v+1)=2^513*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^513 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬513*(i+1)+512<513 := by omega
      have di : 513*(i+1)+512-513=513*i+512 := by omega
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
theorem top_xor (a : Bits) : BitVec.allOnes 512 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 512).toNat) op
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 513) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (513*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 513) (i:=i) (by simpa using hi) _ ok.2
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
    let z := packedOp (r*(BitVec.allOnes 512).toNat) op a b'
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
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 512 then true
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
        packedColumn d (packedOp (r*(BitVec.allOnes 512).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 512
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
  let ls := fun tag => ifUseful3853 (iw != 63 || nl != 0)
    (((g.index k tag).bind (linkedSet g (k-1))).toList ++ (extra3853 g k tag).filterMap (linkedSet g (k-1)))
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

def edge9411 : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 4 && x 8)
def sample9411 (r : Row) (i : Fin 9) := bit r (inputs.getD i.val zero)
theorem raw9411 : List.ofFn (fun i : Fin 9 => inputs.getD i.val zero) = vars 511 := by decide +kernel
theorem samples9411 (r : Row) : List.ofFn (sample9411 r) = (vars 511).map (bit r) := by
  rw [←raw9411,List.map_ofFn]
  rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem edge9411_table : ∀ r : Row, bit r (graphGoal 511) = edge9411 (sample9411 r) := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem conclude9411 (absent : Impossible (graphGoal 511) 13 (vars 511).toFinset) :
    ∀ t, PEqualNP.MetaComplexity.HasCircuitSize 9 edge9411 t → 14 ≤ t := by
  intro t hs
  obtain ⟨C,hf,hsize,correct⟩ := hs
  by_contra! bad
  have hp : proper (graphGoal 511) := by unfold proper; decide +kernel
  have he : (execute C.gates (vars 511)).getD C.output zero = graphGoal 511 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute C.gates (vars 511)).getD C.output zero) = bit r (graphGoal 511)
    rw [←b_read,execute_bits _ _ _ (fun g hg => (hf g hg).1),←samples9411,edge9411_table]
    exact correct (sample9411 r)
  have hout := get_rep (execute C.gates (vars 511)) C.output
  rw [he] at hout
  obtain ⟨k,u,S,hk,run,sub⟩ := extract C.gates _ hf hp (hout.resolve_right (fun h => h hp))
  have all : ∀ a ∈ vars 511, Essential (graphGoal 511) (vars 511) a := by
    have valid : checkEssential (graphGoal 511) (vars 511) (graphPairs 511 8591013460) = true := by decide +kernel
    have ident : (graphPairs 511 8591013460).map Prod.fst = vars 511 := by decide +kernel
    intro a ha
    apply essential_ok valid a
    rw [ident]
    exact List.mem_toFinset.mpr ha
  have eq : S=(vars 511).toFinset := by
    ext a
    constructor
    · exact fun ha => List.mem_toFinset.mpr (sub a ha)
    · intro ha
      obtain ⟨r,s,diff,sep⟩ := all a (List.mem_toFinset.mp ha)
      exact raw_required run _ a sub r s diff sep
  rw [eq] at run
  change C.gates.length ≤ t at hsize
  exact absent k u (by omega) run
def packed85r3 (i : Nat) : Nat := 0xf
def layer85r3 : Packing := (1,0,0,63,0,0,1,packed85r3)
def samples85 : Array (Bits × Bits) := #[(0x60fff,0x221a3),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbf060,0xa736a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc007f,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd4a5c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff58c10),(0x0,0x0),(0x0,0x0)]
def cols85 : IndexTree ColumnInfo := (.leaf [])
def levels85 : Nat → Packing
  | 3 => layer85r3
  | _ => emptyPacking
def index85 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g85 : Forest := ⟨85,3,fun j => samples85[j]?.getD (0,0),cols85,#[[]],levels85,index85,noFactory,noFactorySound 85⟩
def packed179r4 (i : Nat) : Nat := 0x1f
def layer179r4 : Packing := (1,0,0,63,0,0,1,packed179r4)
def samples179 : Array (Bits × Bits) := #[(0xb303f3c0ff,0x1128b1d253),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff4dfc0cffc0,0x51c6447ca),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8e000f00ff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8e924e24ac),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000fff00,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0a28bb830),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeac3002020),(0x0,0x0)]
def cols179 : IndexTree ColumnInfo := (.leaf [])
def levels179 : Nat → Packing
  | 4 => layer179r4
  | _ => emptyPacking
def index179 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g179 : Forest := ⟨179,4,fun j => samples179[j]?.getD (0,0),cols179,#[[]],levels179,index179,noFactory,noFactorySound 179⟩
def packed155r4 (i : Nat) : Nat := 0x3f
def layer155r4 : Packing := (1,0,0,63,0,0,1,packed155r4)
def samples155 : Array (Bits × Bits) := #[(0x6820ffff,0x28a21aa3),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9b03f0660,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8b1a7366a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe3fc00780,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa39c6378a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00007ff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc514a55c),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800,0x54618c010),(0x0,0x0)]
def cols155 : IndexTree ColumnInfo := (.leaf [(2,0,153,0,4)])
def levels155 : Nat → Packing
  | 4 => layer155r4
  | _ => emptyPacking
def index155 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g155 : Forest := ⟨155,4,fun j => samples155[j]?.getD (0,0),cols155,#[[]],levels155,index155,noFactory,noFactorySound 155⟩
def packed341r5 (i : Nat) : Nat := 0x82000200080902000608020080200803e3968c57294884f19283c50500fd43fd42fd32fd41fd31fd21fd40fd30fd20fd10be44de33ee22f611fa00
def layer341r5 : Packing := (15,1,3,63,0,7,1,packed341r5)
def keys341k6 (i : Nat) : Nat := 0x4400005e00000035000000dd0000a30000000000009800000036e9427700000000ac000000fb000000000000005100000000600000000000000000da
def packed341r6 (i : Nat) : Nat := 0x23444bf
def layer341r6 : Packing := (1,0,3,63,0,0,1,packed341r6)
def samples341 : Array (Bits × Bits) := #[(0x680c0180ffff,0x2a1d10a246a3),(0x0,0x0),(0x900ffeff0180,0x10543a870d8a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1ff0070001ff,0x110e06714291c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00007fffe00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc4824558b050),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeef0b8060c060)]
def cols341 : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,340,0,4),(4,0,337,0,4)]) (.leaf [(16,0,325,0,4),(64,0,277,0,4),(256,0,85,0,4)]))
def levels341 : Nat → Packing
  | 5 => layer341r5
  | 6 => layer341r6
  | _ => emptyPacking
def index341 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 5 61 0 8 4 0 keys341k6
  | _ => fun _ => none
def g341 : Forest := ⟨341,6,fun j => samples341[j]?.getD (0,0),cols341,#[[]],levels341,index341,noFactory,noFactorySound 341⟩
def packed119r5 (i : Nat) : Nat := 0x7f
def layer119r5 : Packing := (1,0,0,63,0,0,1,packed119r5)
def samples119 : Array (Bits × Bits) := #[(0xc30e403ff33cc03fff,0x41024290b11cc49513),(0x30ccb80300ccffff300,0x104cb91b4644551f34a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc70f3ffc00f0f003c00,0x45052c7c1ef0f0dbc3a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80fc00000ff0003fff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80fc350d4ee0392aec),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000fffffc000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefb0026098bbaae00b0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaead382e00003000c0),(0x0,0x0),(0x0,0x0)]
def cols119 : IndexTree ColumnInfo := (.leaf [(0,2,85,32,5)])
def levels119 : Nat → Packing
  | 5 => layer119r5
  | _ => emptyPacking
def index119 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => samples119[j]?.getD (0,0),cols119,#[[]],levels119,index119,noFactory,noFactorySound 119⟩
def packed231r6 (i : Nat) : Nat := 0xe413f
def layer231r6 : Packing := (1,0,2,63,0,0,1,packed231r6)
def samples231 : Array (Bits × Bits) := #[(0x85b9c07f87203ff980,0x98c307832190f98a),(0x11a4e7f8019c0301fff,0x80a458a09c4b24a93),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe638f8000e1ffc01e00,0x2238f9326a169c4de2a),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff83f00000fe00001fff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff83f03264f6190c956c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000ffffffe000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddc0024485c962b0050),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff765387000180c0060),(0x0,0x0)]
def cols231 : IndexTree ColumnInfo := (.leaf [(0,4,163,64,5),(0,32,197,2,5),(4,0,227,0,5),(32,0,199,0,5)])
def levels231 : Nat → Packing
  | 6 => layer231r6
  | _ => emptyPacking
def index231 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g231 : Forest := ⟨231,6,fun j => samples231[j]?.getD (0,0),cols231,#[[]],levels231,index231,noFactory,noFactorySound 231⟩
def packed187r6 (i : Nat) : Nat := 0x90ff
def layer187r6 : Packing := (1,0,2,63,0,0,1,packed187r6)
def samples187 : Array (Bits × Bits) := #[(0xc60d0101fccf301fff,0x420515142c47324a93),(0x1093601fe0333fff980,0x1160d0e191150f98a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe71c7fe0003c3c01e00,0x251473e3c7bc3c6de3a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff81f8000003fc001fff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff81f8a8a953b80c956c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000003ffffe000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00b0b162eeaf0070),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdaca8c0c18000080040),(0x0,0x0)]
def cols187 : IndexTree ColumnInfo := (.leaf [(8,0,179,0,5),(1,16,170,0,4),(2,32,153,0,4)])
def levels187 : Nat → Packing
  | 6 => layer187r6
  | _ => emptyPacking
def index187 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g187 : Forest := ⟨187,6,fun j => samples187[j]?.getD (0,0),cols187,#[[]],levels187,index187,noFactory,noFactorySound 187⟩
def packed461r6 (i : Nat) : Nat := 0x2042080100028201011820040080100200400c5c03ab7b4af2c26a11b96108b05807f553faa7fd43fe997f507fa43fd50fe907f442fcabbe44ef19fb88bec23fa00
def layer461r6 : Packing := (15,1,4,63,0,8,1,packed461r6)
def keys461k7 (i : Nat) : Nat := 0x9c0003040399263374cbd11400004c0000000000000040f8000000ec01a32a02
def packed461r7 (i : Nat) : Nat := 0xb87a969bf
def layer461r7 : Packing := (1,0,4,63,0,0,1,packed461r7)
def samples461 : Array (Bits × Bits) := #[(0x8c7603001901ff9c07f,0x4368b440944a38d123),(0x0,0x0),(0x1309803fe6e0180e7f80,0x101829162e2592a4992),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe431ffc018ffe00f8000,0x11a1c0c8b0e06f850a),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff83e00001f00000fffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff83c11089d088445264c),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000001ffffff00000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff801209174b15802850),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeee5c2e000c06003060)]
def cols461 : IndexTree ColumnInfo := (.fork 6 (.fork 3 (.leaf [(1,0,460,0,5),(4,0,457,0,5),(8,0,453,0,5)]) (.leaf [(64,0,397,0,5),(128,0,333,0,5),(256,0,205,0,5)])) (.fork 3 (.leaf [(65,0,396,0,4),(68,0,393,0,4),(129,0,332,0,4)]) (.leaf [(136,0,325,0,4),(260,0,201,0,4),(264,0,197,0,4)])))
def levels461 : Nat → Packing
  | 6 => layer461r6
  | 7 => layer461r7
  | _ => emptyPacking
def index461 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 5 31 2 8 4 0 keys461k7
  | _ => fun _ => none
def g461 : Forest := ⟨461,7,fun j => samples461[j]?.getD (0,0),cols461,#[[]],levels461,index461,noFactory,noFactorySound 461⟩
def packed349r7 (i : Nat) : Nat := 0x7f
def layer349r7 : Packing := (1,0,0,63,0,0,1,packed349r7)
def samples349 : Array (Bits × Bits) := #[(0xc40580c013380fffff,0x450da2d1011a246aa3),(0x0,0x0),(0x1280600ffedcff01980,0x282e0643a54870d98a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe63007ff0071f0001e00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe2306e8f0771f162de1a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff83ff800007e00001fff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe838700c067e0142951c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000007fffffe000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff824048245aa58b0050),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000,0x15c78170b800060c0060)]
def cols349 : IndexTree ColumnInfo := (.leaf [(8,0,341,0,7)])
def levels349 : Nat → Packing
  | 7 => layer349r7
  | _ => emptyPacking
def index349 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g349 : Forest := ⟨349,7,fun j => samples349[j]?.getD (0,0),cols349,#[[]],levels349,index349,noFactory,noFactorySound 349⟩
def packed367r6 (i : Nat) : Nat := 0xff
def layer367r6 : Packing := (1,0,0,63,0,0,1,packed367r6)
def samples367 : Array (Bits × Bits) := #[(0xc0fb332b300330021c393e400fffcccc00,0x405b332b331b331a0c19164c64c7ccccca),(0x332c003f3c003c00060ce33800c00ffffff,0x132c00173c52bc528204e33952d52555553),(0x4030c3c3c0003ffff870fc3fff000f0f000,0xc143c0019501e850b42c07006f0f00a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff83c0fc03ffffc0003f80ffc000000ff0000,0x8140d403d507c007bf80ffc036036ff003a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00fffc000000003fff000000000ffffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffec00ffe800a500a53dfb0002a42a4aaaaac),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000003ffffffffffff000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfa000000c600c6172e4a9338b38000330),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ebf2abc2af82af800000003c03c00003c0)]
def cols367 : IndexTree ColumnInfo := (.leaf [(0,2,333,32,6)])
def levels367 : Nat → Packing
  | 6 => layer367r6
  | _ => emptyPacking
def index367 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g367 : Forest := ⟨367,6,fun j => samples367[j]?.getD (0,0),cols367,#[[]],levels367,index367,noFactory,noFactorySound 367⟩
def packed502r6 (i : Nat) : Nat := 0xff
def layer502r6 : Packing := (1,0,0,63,0,0,1,packed502r6)
def samples502 : Array (Bits × Bits) := #[(0x0,0x0),(0x460831e40ec030024cfffff33cc03fff,0x20010e406d1b460044154711cd2954b),(0x8934c20733003ffdb32b300ccffff300,0x1144001130290b4912b31244544f312),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff31c70c79c3ffc00e3c33c00f0f003c00,0x1114504294347c1ee3c33c36f0f0ebc3a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc1f80f81fc00000fc03c000ff0003fff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc1f80f01f826098fc03c0b0ee02c2ab4),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000ffe0000000fffc0000fffffc000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000ffe00350d4b6ec00e4bbabb00e8),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000ffffffff000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdffe0000026098ffbbeab80002c00b0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeeeaabbd6acb82e0000000c00003000c0)]
def cols502 : IndexTree ColumnInfo := (.leaf [(0,2,340,160,6)])
def levels502 : Nat → Packing
  | 6 => layer502r6
  | _ => emptyPacking
def index502 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g502 : Forest := ⟨502,6,fun j => samples502[j]?.getD (0,0),cols502,#[[]],levels502,index502,noFactory,noFactorySound 502⟩
def packed375r8 (i : Nat) : Nat := 0xff
def layer375r8 : Packing := (1,0,0,63,0,0,1,packed375r8)
def samples375 : Array (Bits × Bits) := #[(0xc0f4cc2400330000c30e4003fff33cc003ffff,0x4054cc24c27330a041024c2930b11ccc495313),(0x332c00fb8003c00030ccb8003000ccfffff3000,0x132c005b9497c526104cb951b546445551f354a),(0x40308f0c0003ffffc70f3fffc000f0f0003c000,0x850c0075501f45052c07c01ef0f00dbc03a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff83c0f00ffffc0000f80fc0000000ff00003ffff,0x8140900c81d80074f80fc03500d4ee00392a0ec),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00fff000000000fff000000000ffffffc0000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffec00ffa029600a58efb002a60a98bbaaae00ab0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000ffffffffffff00000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfa000031800c60baead3382ce000033000cc0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ebf6af37e02af80000003c00f000003c000f00)]
def cols375 : IndexTree ColumnInfo := (.leaf [(0,2,341,32,8)])
def levels375 : Nat → Packing
  | 8 => layer375r8
  | _ => emptyPacking
def index375 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g375 : Forest := ⟨375,8,fun j => samples375[j]?.getD (0,0),cols375,#[[]],levels375,index375,noFactory,noFactorySound 375⟩
def packed439r7 (i : Nat) : Nat := 0xff
def layer439r7 : Packing := (1,0,0,63,0,0,1,packed439r7)
def samples439 : Array (Bits × Bits) := #[(0xc134cc240198015b267007fccf3007fff,0x4114cc25939b28090236532c473692ad3),(0x101c00fb801e002a4db9ff80333fffe600,0x14005b88be118004a92391911523e64a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe62608f0c001ffff38e3e00003c3c007800,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe2220850c03aa87f38e3e170bbc3c1b783a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8380f00fffe0003c0fc000003fc0007fff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe8280900c82c0053c0fc012093b8012542c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00fff00000003ff00000003fffff8000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00ffa03300663ff000d46a2eeadc01b0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000003fffffffffc000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbea00002200443f6b54984c0000900120),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000,0x15d5f6af37c1578000000e0700000e001c0)]
def cols439 : IndexTree ColumnInfo := (.leaf [(4,0,435,0,7)])
def levels439 : Nat → Packing
  | 7 => layer439r7
  | _ => emptyPacking
def index439 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g439 : Forest := ⟨439,7,fun j => samples439[j]?.getD (0,0),cols439,#[[]],levels439,index439,noFactory,noFactorySound 439⟩
def packed491r7 (i : Nat) : Nat := 0xff
def layer491r7 : Packing := (1,0,0,63,0,0,1,packed491r7)
def samples491 : Array (Bits × Bits) := #[(0x44d30c3f333000418e801003ff33ffffcc00,0x510417333318008698d318c71154c7ccca),(0x991c33303fc000a613001ffc00cccc00ffff,0x814133017c528220329552d4a44cd525553),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2220c3c3c3ffff38e3ffe00000f0f000f000,0x414141507d28a383e0781ef0f036f03a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc3c0fc03fc0003c0fc00000000ff0000ffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc3c0ec03e80a53c0fc528a5294bb02a4aaac),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00fffc000003ff0000000000ffffff0000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00fbe8000c63ff00630c6318eeab380330),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000003ffffffffffff0000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7aa0000000802d558440882200002000200),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbebebeaf800000780f03c00003c003c0)]
def cols491 : IndexTree ColumnInfo := (.leaf [(32,0,459,0,7)])
def levels491 : Nat → Packing
  | 7 => layer491r7
  | _ => emptyPacking
def index491 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g491 : Forest := ⟨491,7,fun j => samples491[j]?.getD (0,0),cols491,#[[]],levels491,index491,noFactory,noFactorySound 491⟩
def packed239r7 (i : Nat) : Nat := 0xff
def layer239r7 : Packing := (1,0,0,63,0,0,1,packed239r7)
def samples239 : Array (Bits × Bits) := #[(0x40646e9402700ff870e4f900fff33300,0x2426941a3060783064590641f3330a),(0xa1809318039ff0018338ce00c03fffff,0x208003182a90b0a08138ce12c4955513),(0x30638e3e003e0000e1c3f0fff003c3c00,0x10238e3e11be4646a142d0b4711bc3c4a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc383f03fffc00000fe03ff000003fc000,0x4282d03bc7c01e1efe03ff0360dbfc03a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc03ffc000000000fffc00000003fffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc03ffc03500d4d4f7ec000e4392aaaec),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000fffffffffffc00000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefdc0000260098985cb92a4b8ae0000b0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbd752d843814e0e00000000c0300000c0),(0x0,0x0)]
def cols239 : IndexTree ColumnInfo := (.leaf [(4,0,235,0,7)])
def levels239 : Nat → Packing
  | 7 => layer239r7
  | _ => emptyPacking
def index239 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g239 : Forest := ⟨239,7,fun j => samples239[j]?.getD (0,0),cols239,#[[]],levels239,index239,noFactory,noFactorySound 239⟩
def packed446r7 (i : Nat) : Nat := 0xff
def layer446r7 : Packing := (1,0,0,63,0,0,1,packed446r7)
def samples446 : Array (Bits × Bits) := #[(0x0,0x0),(0x40c00eac0580c0061c9f203fffffff,0x4006ad15a2d100048b28946aaaa3),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1a32933300600ffe59719c030199980,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0a1291330760e47e59719c5b2d9999a),(0x20431c3c007ff0079e7e1ffc01e1e00,0x3143c036870328a5a161c0de1e0a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc383e03fff800007e07fe00001fe000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff4283a03f4780e077e07fe0582dfe01a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc03ffc000000007ff80000001fffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc03ff802604c267ff800150a95555c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000007fffffffffe00000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800002404824575a54962b000050),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000,0xb56c4ac0b8170b8000000180c000060)]
def cols446 : IndexTree ColumnInfo := (.leaf [(4,0,442,0,7)])
def levels446 : Nat → Packing
  | 7 => layer446r7
  | _ => emptyPacking
def index446 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g446 : Forest := ⟨446,7,fun j => samples446[j]?.getD (0,0),cols446,#[[]],levels446,index446,noFactory,noFactorySound 446⟩
def packed223r7 (i : Nat) : Nat := 0xff
def layer223r7 : Packing := (1,0,0,63,0,0,1,packed223r7)
def samples223 : Array (Bits × Bits) := #[(0x4040269404e03f861c9f203fffffff,0x29414608180048b20906aaa83),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe1a1a4db18073fc0659719c030199980,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0a0a44b187523c7659719c5b2d9999a),(0x60638e3e007c00079e7e1ffc01e1e00,0x20238e3e137c99328a5a169c4de1e2a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8383f03fff800007e07fe00001fe000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe8282d03bc7803877e07fe0582dfe01a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc03ffc000000007ff80000001fffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc03ffc03601b367ff8001d0e95557c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000007fffffffffe00000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfdc00002401224575a54962b000050),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000,0x175752b443829c38000000180c000060),(0x0,0x0)]
def cols223 : IndexTree ColumnInfo := (.leaf [(2,0,221,0,7)])
def levels223 : Nat → Packing
  | 7 => layer223r7
  | _ => emptyPacking
def index223 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g223 : Forest := ⟨223,7,fun j => samples223[j]?.getD (0,0),cols223,#[[]],levels223,index223,noFactory,noFactorySound 223⟩
def packed443r7 (i : Nat) : Nat := 0x41081000000000000000cd82d5490f1b305490f182430300bfceea95fe77542ff3ba417f5d520fdaa4907f9504833f334abb799a33ebcab19eee6688bb72ac45f38ce22df4cd0077a55803ed19c01fa88a00
def layer443r7 : Packing := (16,2,4,63,0,7,1,packed443r7)
def keys443k8 (i : Nat) : Nat := 0x2900d300ffcb00a55000a8d2bc8e005a24ad00a70051b600008
def packed443r8 (i : Nat) : Nat := 0x2881155631062082a81d071883530eb20823aa474083558a620c4155675a082aa465a061aa86390620a6b3ad04106a61d04189490d68ac35845586b0d61e3e7aeb4c96c11c0bc499a87831108581600ff597fe55ff58ffd53ff58bfd52ff4cbfd60ff543fd30ff482fe66df957de33fb88bfa00
def layer443r8 : Packing := (16,1,4,63,0,9,1,packed443r8)
def keys443k9 (i : Nat) : Nat := 0x4401bd466f5800005596bbea014800cd200000620001700072000000011e00001660
def packed443r9 (i : Nat) : Nat := 0x8642b2ff
def layer443r9 : Packing := (1,0,4,63,0,0,1,packed443r9)
def samples443 : Array (Bits × Bits) := #[(0xc4d330900330006306801003ff33cc00ffff,0x445330962736282102b156298b11cd925593),(0x107003ee003c000849b001ffc00ccffffcc00,0x50016e217c218008b10d21c86445487cc8a),(0x0,0x0),(0x20823c30003ffff38e3ffe00000f0f000f000,0x21430075507d28a383e0781ef0f036f03a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc303c03fffc0003c0fc00000000ff0000ffff,0x410240320d800d3c0fc0a815054ee0064a86c),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc03ffc00000003ff0000000000ffffff0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc03fe80ce00ce3ff006b0d6358bbab780370),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000003ffffffffffff0000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffba800008800882d6544c0982600002400240),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbefdabcdf02af000000700e03800003800380)]
def cols443 : IndexTree ColumnInfo := (.fork 6 (.fork 3 (.leaf [(32,0,411,0,8),(1,0,442,0,7),(8,0,435,0,7)]) (.leaf [(16,0,427,0,7),(256,0,187,0,7),(2,32,409,0,7)])) (.fork 3 (.leaf [(0,16,170,257,6),(0,256,163,24,6),(128,0,315,0,6)]) (.leaf [(1,16,170,256,5),(8,256,163,16,5),(16,256,163,8,5)])))
def levels443 : Nat → Packing
  | 7 => layer443r7
  | 8 => layer443r8
  | 9 => layer443r9
  | _ => emptyPacking
def index443 : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 5 25 4 8 4 0 keys443k8
  | 9 => lookupWord 5 37 5 8 4 0 keys443k9
  | _ => fun _ => none
def g443 : Forest := ⟨443,9,fun j => samples443[j]?.getD (0,0),cols443,#[[]],levels443,index443,noFactory,noFactorySound 443⟩
def packed463r8 (i : Nat) : Nat := 0xff
def layer463r8 : Packing := (1,0,0,63,0,0,1,packed463r8)
def samples463 : Array (Bits × Bits) := #[(0x11303eb300cc00069402700ff93e403ff,0x11016b322cc8802948a3222391648923),(0x61ccb33c00f0021b18039ff00e3380300,0x214cb33c66f19a0b199a96766e339ab6a),(0x8600c3c000fffc63e003e0000fc3ffc00,0x20003c00a542c23e04be1212b42c4c12),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff080f03ffff000383fffc00000ffc00000,0x503d507001a83bc1c00606ffc0280a),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffc00000003fc000000000ffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00fe800c40313dc03100c4c44a9332cc),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000003fffffffffff00000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdea000008802217442614989800024090),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfafc2af0abc00003800e0e0000380e0)]
def cols463 : IndexTree ColumnInfo := (.leaf [(2,0,461,0,8)])
def levels463 : Nat → Packing
  | 8 => layer463r8
  | _ => emptyPacking
def index463 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g463 : Forest := ⟨463,8,fun j => samples463[j]?.getD (0,0),cols463,#[[]],levels463,index463,noFactory,noFactorySound 463⟩
def packed477r6 (i : Nat) : Nat := 0xc23bb2643ccd0043e65e8858060
def layer477r6 : Packing := (2,4,5,63,0,3,1,packed477r6)
def keys477k7 (i : Nat) : Nat := 0x2400
def packed477r7 (i : Nat) : Nat := 0x61a008041466008081000519842020400008181841640580163069011b020a8c11a0208081020600e043410e0208340820000305171020d070411b0400010145c308381c004681a4c30a005041410000000000000000000000208000000000000008506141000000000000000000037cddb60d4b3ccbb20c2afcbdaf0b8adcb3ac0acaa4a5a809ca5c93a408ea2c87a087c9ec799d8709b4699986498c5f9685694c4f92848914419003e8f43b8e8388dc358d0328c42f8b82c8ac298a026894238882087c1d8701a85c138481083c0d8300a824078180480c018009fd839dd659fd839dd64f3d6559154bdd8650d32f9d6450d32fcd4358932bdd8654d31f5d6554d31fd553585319fd839dd60ddd839dd60bdd839dd60dde771cd60ddd751cd60edd651cd60ddd741cd60edd641cd60ddc735c960edd634c960ddc735c560edd634c560f5d534c550f9d434c9409fe885d930ef96558130ef96458130fd95358130fd943581309fd839dd209fc8759120ddd7350d20fcd434c920ef96458120fd88358120ef963581209fd839dd109fc8759510ddd7354d10fd5534c510ef96558110fd88358110ef96358110fe521481109fc8799a00aed821c266af5811c2669ed829dd659f5819dd64e3e6695644e5e6695633e9e6691233f1e5591233eae6691222ece668ce22f8e448ce22e766695611ed6668ce11f56558ce11ee66688a11fc63388a119dd839dd609dc878cd60afa8858060e7a5558060eba4458060ed88358060cf97358060eda3358060eea2258060ef2115806097d859dd209bd849dd10b79851da00bb9841da00e7a6695600eba6691200f3a5591200eda668ce00f5a558ce00f9a448ce00eea6688a00faa4488a00fca3388a00ef26684600f725584600fd23384600fe22284600
def layer477r7 : Packing := (87,3,5,63,0,10,1,packed477r7)
def keys477k8 (i : Nat) : Nat := 0x301548a7e26a680042826cb1400055561253a08005928bc000210000000031896aae00062c82cd0c1195083b2c88fbb9a4c047973aa90f146c1820102a5d8418b5560330a91c836acec8156a4583f468063960f95ba92075f0800304000001588b4f9c002448000010fc001cc2a86f69d80065b008055ca98e348005bc332e3b0f3c839a0026222404b31a0000579e34d614110004538024006a04208400e0850091c21011c1
def packed477r8 (i : Nat) : Nat := (if i < 1 then 0x7583febaac1ff59560ffae8b07fd64583feaa2c1ff5cd60ffac6b07fd53583fea1ac1ff5c960ffac4b07fd42583fe992c1ff5c560ffac2b07fd51583fe98ac1ff48560ffccca87fd64543feb1aa1ff50d50ffac2a87fd31543feb02a1ff99940ffacaa07fd63503fea9a81ff58940ffa64a07fd60503fea8281ff5d930ffccc987fd754c3feb2a61ff5d130ffac8987fd544c3feb9261ff58930ffa84987fd714c3feb0a61ff54530ffa42987fd604c3fea8261ff50130ffac8907fd63483fea1a41ff58520ffa62907fd60483fea0241ff4c120ffaca887fd63443fea9a21ff58910ffa64887fd60443fea8221ff4c110ffa40887fe66803feb1c01ff58a00ffa65007fd61803fe98c01ff48600df8e1335fe775977f332cbdf99a55bfceeb26fe66593bf2aac97f9dd54bfaecaa6fe66553beb2aa9ef59154f7ccd227bd65912ff3bac7bf99963efcaab1fbe4458eff3baa77f5d953dfccca9f7d6554fdf222a77f9dd43bfaeca1efe6650efebaa87df95543f7ac8a1fde668cfeeb2c67f759233fbaa919dfe7758b7f332c5ef91162fbc66b15fe7750afebb285bf99942f7ac8a17de3350aff3ba657f5d932dfccc995fd744cbdf22265f758d32fba86997ed624cbf733445fb59222fdac7117ed4388aff3bac3bf99961efcaab0fde33587f7112c37f9dd51bfaeca8efe66547beb2aa3f78cd51bfcee98dfd764c77f332637f5d531efcaa98fdd634c7eea9a63fb88931feac298dfe77486febb243bf99921bfae690fde33487f6b1243fd58521feccd08ff565847fab1c23fd54e11feac508ff532846ff3bac1bf99960dfacab077e555837eb22c1ef91160fb8e6b06fd63583ef19ac1fb88960fec22b05fd75183bf2a8c17f5d060f7c88305fd73183ef198c17f5c860fdc44305fd71183fb088c17f9dd50bfaeca86fe66543beaa2a1ef91150efaa6a87de33543fb08aa17f9dd40bfaeca06fe66502febaa81df95540f7aa8a07bd43503ef19a81fb88940bfcee985fd764c37f332617f5d530efcaa985fd744c3df22261f754d30fba86987ee224c3fb08a61fe58130bfcee905fd764837f332417f5d120f7c88905fd73483ef19a41fb50920fda64907ed21483fb08a41fe58120bfcee885fd764437f332217f5d510efcaa885fd73443ef19a217f5c910fdc44887f551443fa98a21fd48510ff2c0887f876803fd33401fe59600ff2c9007f954803fcb1c01fe54e00ff287007f962803fca1401fe4ca00ff2c3007f951803fc98c01fe48600dfccd0077e55803df22401f78ce00fdc45007f611803fcb0401fe54200ff281007f930803fc90401fe44200cfccd2aebe669139f2ac89b799a33ebcab19f9e448cf7733445eb91222f9c67116f666847bb2ac23f58ce11fcc4508ef9601837d33401de95600f7489007da33803f511401fc84600 else (if i < 2 then 0x305060448d0014a6a3c7192a88f2400431a0f0a40c142028e3c60a10182122c0045060a8a447343c004506106a38a2430737205800a180140051028414208c16284860a101820282b848020a3944709044146a78e1208b263c38114a3868545220861208a1208818200a060a82108080a7162a08411b3438690990420c1005028541084040538915042181820120b0c0c002903058808c0a206a71620214708452440620218202031c98c100828e2c586086040400b161822c2871ca050a343a2921830c10c1018100406182c509080c080a1002181810030540086080400b15003187288e30d4f1a0050026cd068520b1320dc80c00290285888020c08048142c4401030120dc9110042019b0d108371a0106e3888020c6e4463054735204020a3891618008302031c48b0c004100c73524300102091cd090c0041c21a0d107351a10e6a30c6a3c6161800a1801404012306002881440a105082841400a005002801400a005002801400a0051400a003001800a48012300148863c2a23c501044a214f0c8864278a4431e1511e28f0a88f10586020894429e180822510a78780bbf1df26f43787bafdcdee5771fb89dbaed6b68db2bd8bec0f5dfadbd5cea97523a7dd34e957483a1fd05e7df3c79cfcda668330b95cca7e50b25d91ac8363cb1a18bcc5462530e585ec1ae086fff7ebbebdf0ef5f79bbc3dd96ea373db94dc56e036edb73db4ed9b6abb52da0ecdf662b2758eac5b619b02d7c6bc95d0ade564eae354fa96d44a9ef4e3a67d29a909462a2050968153f69f14f1e7753a69c94dfa6d53569a14cd66272ff9794b425792a8946c9ae4bd243914486e40f1d78e546f63611958b9c59a29713e891c4061e90bd8584256111074830414e047016804bff1fc2fb87d5be41f06f537953c75ddaee0762ba8dd02e74730394dc8ce16704b7f1bdede26e3b679b22d766b4b4e5a20d03669b319956c8963e3169854c015fa2ef5760b875af2d4567ab30591ac59612ab65512a1d4e6a58522286d3f29ec4ec271133698e4b2a56125091b47923951788af43fa1590928204099fc4fc87d73d39df8ee274839d9c48de06e336b1a98cd065b3191894bf85ef2ea16e4b5859f2be956ca6451e27a938497e4ab24811d48b444621590247c03cc1d18e3c6da35919b8c8c6102ed1690adc55429d14489d44d025b127090446822710d08344001f30f307643981bf0d906943301840bb85a82ba14909a84a023610707983981b20cc05c02ac13c08a03e81a40b804801d80b803400d0007fd65593ff332a9ff5d563ffacab1ffd7458ffeb22c7ff55163ffae4b1ffd7158ffeb82c7ff99953ffac8a9ffe6650ffeb2a87ff59162ffac6b17fd4358bfeb1a85ff59132ffacab0ffd63587fea9ac3ff58961ffa64b0ffd63547feb2a63ff58931ffac690ffe7 else 0x10c08718632121050c20900282104645840000184c120302c32a9824254606820846e08428ac45050448320172218011a801093111a8011212117121110c84648445043cd04182c4890c5090a40d1208a120461990b0870d15102881303a22a362488a284842365210d1091b891a28a12008d1784384226a21e1a11b342960c1160680688586045460458484248c48a2044c3044c2211c21316113161131410a251228610d8610018804010088474801006806c840684901202822028246090121101210f1214204742086c20a20302806ca7a201372150b10548722013624422283888a0871208512084121a1003a53d0c01a90c05862643b0c01a12192121c3450038700287002490e0461610a7823a1422514238142231420a3c20d08b132074905005001182a38d920200a0200a1991a182031c6890c186207471038d8e00286004142030200f0c801400a0061181c183012074908184207470818454686100c71b242046060b094471a3c2061071b1c0050c00a02009182141820120e8c801820c1060941a185052000a160821c08d0e08218283012090c14203002858208b0c14200143410529b911c64b213c818d8885240060200a0028810a101018e706000c006003001805c70614147022458008800383800860a100c722305080c0891600230))
def layer477r8 : Packing := (311,2,5,63,0,13,1,packed477r8)
def keys477k9 (i : Nat) : Nat := 0x170e23149742594d40571b8ba38896cb27d68b388f29ef59307753ab0d75a0b1425cf31f6d34ab9c7ee5024e3c6e6dc7db06047a453453e82a97d15c47ec9613c04db44890e7b5e601f119845261c3763c264c9dc59f0eb857fa18080804d071c3e645719c605b3ac0df3413c9a7e9ce30191a7ace413b23a321c300000cd34a0003da3c0b87a0000001aaa979fbd8000cd3000000018e70ab0b13b19740e9a8b52e400000000009bfe6705411ea22284b8190006054000000709800112e00046a5a2800145518b80029a0efd519c2b2dda62d83fb8d78a2000000441c0014a1e35b2fc0000000000000000c83c85f9e11bb8e4f22f11b8b3f2b000744d53582a7350a0ad5641ad543180941e6717a9198000000134d8f9122afc101ca8b9cc4a9426007e85e51818e730413800077d92c0803925c527a9e41166e9345a4209f4b5703eb491b64dc71ffb1a4bc0cc075200a4a400035f2c6800143100073bfa60e5ce0bc9d86424954090410a4ca3063e1be4000a0d0000a4fdab42192bfc0b65e000f5bb1eb8960e00000000450e107617c90a2000011b225ac282e206c8968000000000226ea5bb2877bea340008bbb13fc390f7135a32b9c3c4c224e4cd079894a20107d2c4589cb6e1ceb781e40feb2c12b60c7c1147fd10826568f04760bae0c4753366b0fc6567318aa28fc4411d130b139590c2b526fc834a003a743c21063fa81d001177430c432709af45bec7414008ecd13e0ac7c6c514e52d6193ca33978f1b1949bb9d17cd8820c1c7cc5a38e2dc15a5946a55890a1720600b0d12201960024483146c78700b0000001d501000805200543b00a30b804234000064c52100391001428036800c1154c283a24e18001400c00e1e080012cd810a8605a0000385824c1000f1aa0eb4864248004583801c4010c
def packed477r9 (i : Nat) : Nat := 0xadc4d5138d38c2c474e44c30b11b40f33230b11a40f38b4053bd2b030a7053913aa30a68540f38b114ece44c30adc46903ce90c2b614e44e2c44b940f30c2b511c40f3a230ad0540f39e30b13440f38430b1513ccd9d1346d138c2d234462d39130d1169d03cc35014e84a30b13739130c2c4d503cc31d11b44e2ce0443513cb14e4471503c744e14714e4471503c60442d13cb1ba2241a7d4f19cb366678c316e2b2504949111f8378648b41442343c06009c1081b02a03c048003fe66ff597fd64ff553fd63ff54ffd43ff58bfd42ff4cbfd61ff547fd31ff487fd60ff183fd50ff503fd30ff483fd10ff802fe66df957be44f78cfee22fd847fa00
def layer477r9 : Packing := (29,1,5,63,0,11,1,packed477r9)
def keys477k10 (i : Nat) : Nat := 0x310afa360f231e00a2d252c0000332c4cd0000000fb6e041292b3c81ec0750002be7265953800009c4c40000005e8a900000040482
def packed477r10 (i : Nat) : Nat := 0x120f1ff
def layer477r10 : Packing := (1,0,5,63,0,0,1,packed477r10)
def samples477 : Array (Bits × Bits) := #[(0x40c0c401600c001087200ffe4ce00ffffff,0x404503682d0400012825060468241aa83),(0x0,0x0),(0xa3012801800ffe6365c00c01b73ff006600,0x2100282b81642e2165c26c4c9522713662a),(0x104263001fff0018c79fff001c7c00007800,0x22301ba0f01c842960f01dc7c160b781a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe38383ffe000001f07e000001f8000007fff,0x22828387c03c079f07e06c0d9f80743a547c),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc03fc000000001ff80000001fffffff8000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc03f8250128251de801482916a958ac0150),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000001fffffffffe00000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8002601302617bd6970ae000160b00160),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdd6d5c7805c0b80000018030000180c00180)]
def cols477 : IndexTree ColumnInfo := (.fork 15 (.fork 7 (.fork 3 (.leaf [(4,0,473,0,8),(8,0,469,0,8),(16,0,461,0,8)]) (.leaf [(64,0,413,0,8),(128,0,349,0,8),(1,0,476,0,7),(256,0,221,0,7)])) (.fork 4 (.leaf [(68,0,409,0,7),(136,0,341,0,7),(0,4,153,320,6),(0,8,85,384,6)]) (.leaf [(0,64,408,5,6),(0,128,340,9,6),(1,64,408,4,5),(1,128,340,8,5)]))) (.fork 8 (.fork 4 (.leaf [(12,0,465,0,5),(17,0,460,0,5),(20,0,457,0,5),(24,0,453,0,5)]) (.leaf [(65,0,412,0,5),(72,0,405,0,5),(80,0,397,0,5),(129,0,348,0,5)])) (.fork 4 (.leaf [(132,0,345,0,5),(144,0,333,0,5),(192,0,285,0,5),(256,4,153,64,5)]) (.leaf [(256,8,85,128,5),(260,0,217,0,5),(264,0,213,0,5),(272,0,205,0,5)]))))
def levels477 : Nat → Packing
  | 6 => layer477r6
  | 7 => layer477r7
  | 8 => layer477r8
  | 9 => layer477r9
  | 10 => layer477r10
  | _ => emptyPacking
def index477 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 4 0 5 1 0 keys477k7
  | 8 => lookupWord 29 106 6 11 7 0 keys477k8
  | 9 => lookupWord 103 353 7 13 9 0 keys477k9
  | 10 => lookupWord 9 41 6 9 5 0 keys477k10
  | _ => fun _ => none
def g477 : Forest := ⟨477,10,fun j => samples477[j]?.getD (0,0),cols477,#[[]],levels477,index477,noFactory,noFactorySound 477⟩
def packed383r9 (i : Nat) : Nat := 0x1ff
def layer383r9 : Packing := (1,0,0,63,0,0,1,packed383r9)
def samples383 : Array (Bits × Bits) := #[(0xc003c4b33009000acc00330000861c30c393e4003fff3333cccc003ffffff,0x400144b33009309accc2b330a0020c10009164c2930b1111ccccc49555313),(0x32ccb00003eae000cf0003c00031860ccb2e338003000ccccfffffff333000,0x12ccb000016ae525cf149bc526108204cb2e33951b5464444555551f33354a),(0x4000c28c3c330000f00003ffffc63870f3cfc3fffc000f0f0f0f0003c3c000,0x28c1433001df00079501f422850514b42c07c01ef0f0f0f00dbc3c03a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9830f030fc03c0000fffffc0000f83f80fc0ffc0000000ff00ff00003fc0000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff88305030d403c007df541fc007ef83f80fc0ffc03780deff00ff003dbfc00fa),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe03f003f0003fffff0000000000ffc000fff0000000000ffff0000003ffffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa03500390003f20760001d00074ffc000fff00003500d4eeee0000392aaa0ec),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0003ffffc000000000000000ffffff0000000000000ffffffffffc000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffec0003fffe800a580029600a58ef7dfb0000002a60a98bbbbaaaaae0000ab0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000000000000000fffffffffffffffffff00000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbffe80000000c600031800c60bdd72eaeb4a93382ce000000003300000cc0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000,0x57caafc62abc0df800abe02af800000000000003c00f0000000003c00000f00)]
def cols383 : IndexTree ColumnInfo := (.leaf [(0,2,349,32,9)])
def levels383 : Nat → Packing
  | 9 => layer383r9
  | _ => emptyPacking
def index383 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g383 : Forest := ⟨383,9,fun j => samples383[j]?.getD (0,0),cols383,#[[]],levels383,index383,noFactory,noFactorySound 383⟩
def packed510r8 (i : Nat) : Nat := 0x24210010025a4e5048c0062ba5e2c07fd72bfcefbf99bee997ee22
def layer510r8 : Packing := (5,1,4,63,0,7,1,packed510r8)
def keys510k9 (i : Nat) : Nat := 0x1809000000a3b1100
def packed510r9 (i : Nat) : Nat := 0x261459e6ff
def layer510r9 : Packing := (1,0,4,63,0,0,1,packed510r9)
def samples510 : Array (Bits × Bits) := #[(0x0,0x0),(0x21810303b32003ab002c00c000861c30c393e400fff3333cccc00ffffff,0x800101b32001ab42ad0ad0a0020c100091650a50b1111cccd12555513),(0x42468c04003a4ccc003000fff31860ccb2e33800c00ccccffffffcccc00,0x428400000a44cc09b026427108204cb2e33846c464444555447cccc4a),(0x84081098c3cc70f0003fff000c63870f3cfc3fff000f0f0f0f000f0f000,0x88c14c50f007b41f01e422850514b42c1f01ef0f0f0f036f0f03a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1870e0e0fc0f80ffffc000000f83f80fc0ffc000000ff00ff0000ff0000,0x10850a0a0d40e80fd1fc07e07ef83f80fc0ffc0de0deff00ff00f6ff00fa),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe07f00ff000fff00000000000ffc000fff000000000ffff000000ffffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe07f00fe000ffe009d0274274ffc000fff0002d42d4eeee0002e4aaaaec),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000fffff00000000000000ffffff000000000000ffffffffff000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000fffff00000d60358358ef7dfb000000398398bbbbaaabb80003b0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000ffffffffffffffffff0000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffe0000000000980260260bdd72eaeb4a92e0ae000000002c00002c0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef7ad5b572ab12b02e00b80b800000000000003003000000000300000300)]
def cols510 : IndexTree ColumnInfo := (.fork 5 (.fork 2 (.leaf [(0,32,476,2,8),(16,0,494,0,8)]) (.leaf [(32,0,478,0,8),(64,0,446,0,8),(0,2,348,160,7)])) (.fork 2 (.leaf [(8,0,502,0,7),(2,32,476,0,7)]) (.leaf [(4,64,442,0,7),(32,128,340,10,6),(256,16,238,0,6)])))
def levels510 : Nat → Packing
  | 8 => layer510r8
  | 9 => layer510r9
  | _ => emptyPacking
def index510 : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 10 0 7 3 0 keys510k9
  | _ => fun _ => none
def g510 : Forest := ⟨510,9,fun j => samples510[j]?.getD (0,0),cols510,#[[]],levels510,index510,noFactory,noFactorySound 510⟩
def packed255r8 (i : Nat) : Nat := 0x107188400328d4e2527640800653f4a2c07fd70bfcefef5d3ee987fa00
def layer255r8 : Packing := (5,1,4,63,0,7,1,packed255r8)
def keys255k9 (i : Nat) : Nat := 0x5b0000a490121900
def packed255r9 (i : Nat) : Nat := 0x21cc9966ff
def layer255r9 : Packing := (1,0,4,63,0,0,1,packed255r9)
def samples255 : Array (Bits × Bits) := #[(0x4101010591b009a50027003ff0861c30c393e400fff3333cccc00ffffff,0x909000a502a30280b0020c100091640a40b1111cccc12555413),(0x8286860a024936c60039ffc0031860ccb2e33800c00ccccffffffcccc00,0x828200000912c609a909c26108204cb2e33846c464444555447cccc4a),(0x30c1818cce38e38f8003e00000c63870f3cfc3fff000f0f0f0f000f0f000,0x1040808cce38e38f847be4791e422850514b42d1f11ef0f0f0f136f0f13a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc30e0e0f0fc0fc0ffffc000000f83f80fc0ffc000000ff00ff0000ff0000,0x410a0a050b40b40ef1fc01f87ef83f80fc0ffc0de0deff00ff00f6ff00fa),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0ff00ff000fff00000000000ffc000fff000000000ffff000000ffffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0ff00ff000fff00dd00dd374ffc000fff0003d43d4eeee0003e4aaabec),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000fffff00000000000000ffffff000000000000ffffffffff000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000fffff00000d600d6358ef7dfb000000398398bbbbaaabb80003b0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000ffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefbf7f70000000000980098260bdd72eaeb4a92e0ae000000002c00002c0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbef5d5daf4b64ad10e014e03800000000000003003000000000300000300),(0x0,0x0)]
def cols255 : IndexTree ColumnInfo := (.fork 4 (.leaf [(0,4,187,64,8),(4,0,251,0,8),(8,0,247,0,8),(16,0,239,0,8)]) (.fork 2 (.leaf [(32,0,223,0,8),(2,32,221,0,7)]) (.leaf [(64,4,187,0,7),(1,16,238,0,6),(128,8,119,0,6)])))
def levels255 : Nat → Packing
  | 8 => layer255r8
  | 9 => layer255r9
  | _ => emptyPacking
def index255 : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 9 0 7 3 0 keys255k9
  | _ => fun _ => none
def g255 : Forest := ⟨255,9,fun j => samples255[j]?.getD (0,0),cols255,#[[]],levels255,index255,noFactory,noFactorySound 255⟩
def packed503r10 (i : Nat) : Nat := 0x1ff
def layer503r10 : Packing := (1,0,0,63,0,0,1,packed503r10)
def samples503 : Array (Bits × Bits) := #[(0x20818260c0f4cc240033000110855b267000fff0c30e4003fff33cc003ffff,0x82204054cc24c27330a000000902330a30b041024c2930b11ccc495313),(0x4302038332c00fb8003c0002231aa4db9fff00030ccb8003000ccfffff3000,0x100028132c005b9457c51600108004a9517516104cb949b526445549f352a),(0x844c4c040308f0c0003ffffccc6338e3e000000c70f3fffc000f0f0003c000,0x444400000850c00b5502f4442338e3e04e04e45052c13c04ef0f015bc05a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff187070183c0f00ffffc0000f0f83c0fc0000000f80fc0000000ff00003ffff,0x108505008140900c81d80074f0f83c0fc00d40d4f80fc03900e4ee00392a0ec),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe07f801fc00fff000000000ff003ff000000000fff000000000ffffffc0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe07f801ec00ffa029a00a68ff003ff000ac8ac8efb002b20ac8bbaab600ad0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80001ffff000000000000ffffc00000000000ffffffffffff00000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80001fbfa000031400c50bbbdc00000c90c90baead32c2cb000032800ca0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000ffffffffffffffff00000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeff7d40000000021800860ffef7f6b548e08e00000023008c0000230008c0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef7ababf7ebf6af37e02af800000000000f00f00000003c00f000003c000f00)]
def cols503 : IndexTree ColumnInfo := (.leaf [(32,0,471,0,10)])
def levels503 : Nat → Packing
  | 10 => layer503r10
  | _ => emptyPacking
def index503 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g503 : Forest := ⟨503,10,fun j => samples503[j]?.getD (0,0),cols503,#[[]],levels503,index503,noFactory,noFactorySound 503⟩
def packed495r8 (i : Nat) : Nat := 0x104182000000000000000062b93e13c6cc15243c6090c0c02ffa2130bfd864c3f758d30ff9604c33f9de66d7e779579f99a55ede668cfd795633eee6688bf38ce22dfa77803be99a00fda33803fa88a00
def layer495r8 : Packing := (15,2,5,63,0,7,1,packed495r8)
def keys495k9 (i : Nat) : Nat := 0x5d9355002bcc3c806ec6006080001a1909804a8000477014
def packed495r9 (i : Nat) : Nat := 0x1013663891851030810262882848c28499882050cc98b2062073a64a528530b98818304d3261c628330d98f18a10e3662462472e646540a08f38b9a728d2e640538d9a39a088c2e68ce9a234c9a32e68a58889ec7099e5d14a480f6348a21f8661503c0a812003febb7fe66ffaebff597feb1ffd53ffac5ff4cbfeb87fd60ffa61ff482ff3befe66efcabf78cff7117fa00
def layer495r9 : Packing := (18,1,5,63,0,10,1,packed495r9)
def keys495k10 (i : Nat) : Nat := 0x359280000b70000000816c0016313a800000000000000000035e00000000000000000000640000029028000161d6799620000003da00c20000000048
def packed495r10 (i : Nat) : Nat := 0x31cd59a5ff
def layer495r10 : Packing := (1,0,5,63,0,0,1,packed495r10)
def samples495 : Array (Bits × Bits) := #[(0x421898303ecccacc006600010191ba50013800fff0e1c9f2003fff999800,0x8881016cccaccc366618000909a530d198630f060c8b261930f99998a),(0x8c20e0ccb000fcf00078000286024c6001cfff000306719c003001ffffff,0x400a04cb0005cf14578a28082000c65154a8b514102719ca4b524aaaa93),(0x110c30100c30f0f00007fffcc18e38f8001f000001c387e1fffc001e1e000,0x41000003050f00132a09c408e38f808df04608d4285a1611c08de1e04a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe2104060f03f00fffff800030e0fc0ffffe0000001fc07fe0000001fe0000,0x20503500f540f800790a0b40ef03e001e03dfc07fe00d806dfe003a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc1f807f003fff0000000003f00fff000000000001fff8000000001ffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc1f807b003ffa0029a014d3f00fff00aa80554aa9efd8001590ac955556c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0007fffc0000000000003fff000000000000001ffffffffffffe000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0007efe80000030c01863bf700000c300618c30b9725498e2c70000630),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000000003fffffffffffffffffe0000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbf75000000000021001082f5d4b6108c0a4608c00000001100880000440),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbefdfafcaaf0abe055f0000000000f000780f000000001e00f00000780)]
def cols495 : IndexTree ColumnInfo := (.fork 9 (.fork 4 (.leaf [(32,0,463,0,9),(1,0,494,0,8),(4,0,491,0,8),(8,0,487,0,8)]) (.fork 2 (.leaf [(64,0,431,0,8),(256,0,239,0,8)]) (.leaf [(2,32,461,0,8),(0,4,171,320,7),(0,64,426,5,7)]))) (.fork 5 (.fork 2 (.leaf [(0,256,227,12,7),(128,0,367,0,7)]) (.leaf [(65,0,430,0,7),(68,0,427,0,7),(260,0,235,0,7)])) (.fork 2 (.leaf [(264,0,231,0,7),(1,4,170,320,6)]) (.leaf [(8,4,163,320,6),(129,0,366,0,6),(136,0,359,0,6)]))))
def levels495 : Nat → Packing
  | 8 => layer495r8
  | 9 => layer495r9
  | 10 => layer495r10
  | _ => emptyPacking
def index495 : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 5 29 3 8 4 0 keys495k9
  | 10 => lookupWord 6 57 2 9 5 0 keys495k10
  | _ => fun _ => none
def g495 : Forest := ⟨495,10,fun j => samples495[j]?.getD (0,0),cols495,#[[]],levels495,index495,noFactory,noFactorySound 495⟩
def packed507r10 (i : Nat) : Nat := 0x1ff
def layer507r10 : Packing := (1,0,0,63,0,0,1,packed507r10)
def samples507 : Array (Bits × Bits) := #[(0x8218980c00f4cc240066000441046306800800ffe499fffffccf3001ffff,0x888040054cc24c2e661800000210298698630e00882a61c473314a98b),(0x10c20e032ccc00fb800780008a698849b000fff001b6656600333ffff9800,0x400a012ccc005b944f8a2802288008b28aa8b514922566a491155279a92),(0x0,0x0),(0x2104104c30f08f0c0007ffff338e338e3fff000001c78678003c3c001e000,0x443050850c00eaa07d128a128a381f01e03dc786780dbc3c075e03a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc61860703f00f00ffff80003c3f03c0fc000000001f80780003fc0001ffff,0x420820503500900c81d000e3c3f03c0fc0580580b1f807801c3b800e15074),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff81f807fc000fff000000003fc003ff00000000001fff800003fffffe0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff81f807ec000ffa029a014d3fc003ff00554554aa96dd801592eeaad80568),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0007fffff000000000003ffffc0000000000001ffffffffc0000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0007fbffa000031c018e3ffffc0000658658cb1ff77d59e0000ce00670),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000000003fffffffffffffffffe0000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbf75000000000021001082ed556d6544604608c00000011000008800440),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbdf7dfabcaaf6af37e055f00000000000780780f00000001e00000f000780)]
def cols507 : IndexTree ColumnInfo := (.leaf [(64,0,443,0,10)])
def levels507 : Nat → Packing
  | 10 => layer507r10
  | _ => emptyPacking
def index507 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g507 : Forest := ⟨507,10,fun j => samples507[j]?.getD (0,0),cols507,#[[]],levels507,index507,noFactory,noFactorySound 507⟩
def packed447r10 (i : Nat) : Nat := 0x1ff
def layer447r10 : Packing := (1,0,0,63,0,0,1,packed447r10)
def samples447 : Array (Bits × Bits) := #[(0x181312ccc02400acc00cc000591b009a50027003ff3333cccc00ffffff,0x81112ccc02589acd8acd8a00909000a562a36298b1111cccd92555593),(0x201c0000fab800cf000f0000a024936c60039ffc00ccccffffffcccc00,0x1400005ab885cf086f08600000912c621a921c864444555487cccc8a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8c460a30f0cc000f0000ffffcce38e38f8003e00000f0f0f0f000f0f000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff84420a3050cc03df003e543fcce38e38f817be1785ef0f0f0f076f0f07a),(0x10080c3f00f0000fffff0000f0fc0fc0ffffc000000ff00ff0000ff0000,0xc3500f001df541f001e50b40b40ef07c00781eff00ff0036ff003a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0700fc000fffff000000000ff000fff00000000000ffff000000ffffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa0500e4000fc836000340034ff000fff00150015054eeee000064aaa86c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800fffff00000000000000fffff00000000000000ffffffffff000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800ffffa00338003380338fffff00000d600d6358bbbbaaab78000370),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000fffffffffffffffffff0000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ea0000000220002200220af4b64ad109814982600000000240000240),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000,0x5badf18aaf037c00abc0abc00000000000e000e03800000000380000380)]
def cols447 : IndexTree ColumnInfo := (.leaf [(4,0,443,0,10)])
def levels447 : Nat → Packing
  | 10 => layer447r10
  | _ => emptyPacking
def index447 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g447 : Forest := ⟨447,10,fun j => samples447[j]?.getD (0,0),cols447,#[[]],levels447,index447,noFactory,noFactorySound 447⟩
def packed479r11 (i : Nat) : Nat := 0x1ff
def layer479r11 : Packing := (1,0,0,63,0,0,1,packed479r11)
def samples479 : Array (Bits × Bits) := #[(0x813000f02400acc00cc000101009a50027003ff0c393e400fffffffff,0x11000502481acc82cc820000000a520a320883000916482483555483),(0x301cb32cab800cf000f0008686936c60039ffc00cb2e33800c00cccc00,0x1014b32cab98dcf18ef18e8282912c663a963d8ecb2e33996d96cccd9a),(0x44600030cc000f0000ffff1818e38f8003e00000f3cfc3fff000f0f000,0x4200000cc015f001654170808e38f809be09826514b42c27026f0f02a),(0x8080c3c0f0000fffff0000e0e0fc0ffffc000000fc0ffc000000ff0000,0xc140f000df540f000ea0a0b40ef03c00380efc0ffc016016ff001a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0700fc00fffff000000000ff00fff00000000000fff000000000ffffff,0x10500d400fc83e0003c003cff00fff001b001b06cfff000074074aaa87c),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800ffff00000000000000ffff00000000000000ffffffffffff000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800fffa00328003280328f7f700000d200d2348aeb4a9358b58000350),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000ffffffffffffffffff000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefea0000002300023002305d5d4ad109c149c270000000260260000260),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefadf2abf037c00abc0abc0000000000e000e0380000000380380000380)]
def cols479 : IndexTree ColumnInfo := (.leaf [(2,0,477,0,11)])
def levels479 : Nat → Packing
  | 11 => layer479r11
  | _ => emptyPacking
def index479 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g479 : Forest := ⟨479,11,fun j => samples479[j]?.getD (0,0),cols479,#[[]],levels479,index479,noFactory,noFactorySound 479⟩
def packed511r6 (i : Nat) : Nat := 0x206b9eb365c629ca460120
def layer511r6 : Packing := (1,7,6,63,0,0,1,packed511r6)
def keys511k7 (i : Nat) : Nat := 0x70
def packed511r7 (i : Nat) : Nat := 0x20c20f71b4e2172bb3009849ae365c629ca460120
def layer511r7 : Packing := (2,6,6,63,0,3,1,packed511r7)
def keys511k8 (i : Nat) : Nat := 0x88000
def packed511r8 (i : Nat) : Nat := 0x70304083d910200000002a50305210004280801781000016503c33c585c31c5840000385060800000000000000000000000000000d4e8f258cb85aac95eac54a833095492270d7e3d9e0ea6caf5429b4aa3cfc78391b0cc602d1509c48210f06c30150903c18090300c00a7cdc22c1a3a6587f19cc961d7460d43b39dc42e58760d32a6bdc4a65a625d80ab9dc32a58450980a3ddc32e99850870f998c361d7460140979cc96e17450d30979ccb6617450d30f19d9861d7450d30c79cb9691744c93097b9c42e57660130f1b9876517460130f999872917360130cf98ba2916360130d9d9b761d4360130db98ba6114360130bb99c85d14360130f999875d14360130ed99a85d1435c130dd99b45d1325c130abb9c82c1a425d20aeb9c62c1a425d20cbe9b8688a05d120cee9b6688a05d120bba9c82c17450920bea9c62c1745092096f8c96d8a760120aeb9c629ca460120c1ddb96ceaa61c8788fdcaaed8721e6689bdcaaed8721e4489edcaaed8721e22c3b9b96d2aa60080a1f9c9aaa7760080a2f9c9aaa6660080a3b9c9aa8a460080a3b9c9aaa4460080a3d9c9aaa3360080a3e9c9aaa2260080a1f9c9aaa885c070a4f9c9aaa665c070a5b9c9aaa445c070a5e9c9aaa225c070c9b8ba61d7460140b1d8c961d7360130b598c95d1435c13089f9caaed8721e00
def layer511r8 : Packing := (48,5,6,63,0,9,1,packed511r8)
def keys511k9 (i : Nat) : Nat := 0x2257400c0bbd766e9a508243200065000334e302dab19c87c7d55374ed3146800000c8592a3981961ecf721170fa0a240a27800b3ea6bbc5900106000000000000200713225a829e4f96b0481038018854120064
def packed511r9 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x9123388bec73bc8919c45af628ca061d80ab7b694cceec056bdb4a6666602b5edb12e4a301c6f25d8725180c3f952c3ae8c063bca9a22446032de54cef223019af2a66691180af3b694cc66c0579cb9912336030fe54b0eb93015eb6d29988980af597322444c063f9b9aa9802035dcda554c01014fe6e6aa60080b77369553004069f9a729d802034fd554eec0101abeaaa6660080f1f4ef33300406bbaaa29180203cdd3b948c0101eae998a460080c7f554ca3004071fa776518020397d33328c0101cee6517460080b7717522300406bbaaa91180203cdd3bc88c0101eae99a4460080e77328a1b00406bdaaa8cd80203ced3bc66c0101eb699a3360080f7314919b004073d9948cd80203dcd22466c0101afaaaa2260080f3d4ef11300407ba8a4889802039f4ca444c0101eea9122260080f79467113004047bdb4aa9985c23eed9d54cc2e17766cca05d1708f7974cc488b847dcba662335c317f55510cb0e14bfaed9899870c77d55443283866beaa999941c395f444ccca0e14efaed9891070ad7d76cb4883872be8865a441c395ecc4cd220e1cb7a226664c70e73d112232638769e66911931c3977444ccc90e19ebaaa4464870e75d11223243876ae66911921c29f75db31110e1cbba219688870af5d76ca4443873ae88652221c39d6cc489110e1dab65a4488870e79d10c9c4438778e4464e221c397b444ccc88e1ceda224464470ed6ccd223223873e688889911c3bd322444c88e197e6e6aa5c070abf373552e03869f9a82a1701c34fd55510b80e1b3eaaa665c070f1f511332e0386dbaaa911701c3cdd44488b80e1f2e99a445c070dbd555112e03879ea88889701c3ed522444b80e11ef2e99891160b77370502e8a04fb8ba5d180503cdcc3ae8c02811ef6d2aa661308f7b6854aec9847bcba662444c2aee5cb0eb9a615e72e57450d30af9972b92649853f8b961d804c29fc5cb0cc0261e7661d7360130f73308a1b009855f8b95d9704c2afc5cae8b8261f665d1435c130a9fb6d4ccee9056bdb6a66444823de5d331222415b76da998cd20af5972ba2849053f8b961d80482ddcda153444016ee6d0a7a22009fb3675530f0059fabb61c87802e7cdb1313bc01e3e61c8799a00f1f5113bccd005eb9b626244803cdcc390f224017ae6d88791200f375113bc89007aba8899a44803e5d3bccd224017b66d8988ce009fb174c3c670079da889de33803d6d444cd19c01f369de668ce00f7351122467007d9a7791233803f4d3348919c013ee6d0a94ca00bdd36c4c4450079e98721e22802f74db10f11401e7aa227788a00f7551122445007daa7791222803de54446711401f729de3388a00ff148919c450053bdb42a6888023deda153444013ee6d2aa602009f7175223010041fdb9aa98721e1fcdcd54c010117e6e6aa5c070 else (if i < 2 then 0x61fe62916360130f7b308b1b00985fd8ba50d804c2fecdba86c0261ef661d4360130f7b30ca1b00987f998450d804c3fccba286c0261fe65914360130df7148d13009879f9875c9804c3ddcc2284c02617f62e93260130f7b30e99300987f98a44c9804c3decc2264c02613ef6d2aa60130f3bb0eb9b00987b9d8450d804c2fecd9d54b826177e6de995c130df7168d42e0984ff8baa21704c36fcd42e8b8261f6e651745c130fbb366ba2e0986fd9a858d704c3eecba2c6b8261bf66a1435c130fbb2eca1ae0987f998450d704c3fccb2286b8261f6e5d1425c130dfb350992e0985fd9b44c9704c3eecba264b8261ff2689325c130ff9304992e09855fdb7a65704c3adeca2e8b8261f675d1435c130fb72e8b8280986fb8b0690974827eed9d54c3a411ffaeca961d20cfb95251b0e9056fdb6a66774823fe5d3313ba411ff2ea77651209ff361552e89047febb2a5744833deda152ba2419fb6c8a95d120adfb6d4cae89047fcb96a1744823fe5d330ba2416fe6e0a05d120bdf36c502e8906fe9a2281744823fe5d2e8c9a415bf6da995cd208ff972d42e69056fdb6a65434823fe5cb50a1a411ff2e5a750d20af7972ba286905becb868943483fd4582e8a12417ee6d2aa60120bdf36c53b00907bd8b361d804837dc53948c0241eee61ca4601209ff174ba300905bf9b85d180483cfcc3ae8c0241bee291a360120f3f30eb9b00907bb98450d804827deda554c024157f6de995c120eb7b28ba2e0907dad7450970483fe4992e0982411ff6dca9a22009fbb675530f0047febb2a5878033ee54946c3c011ffaeca95d2008ff972d42e90055fcb961d748023fe5cb50b9c011ff2e5a850e008ff972d3a870047fcb96a1728023fe5cb50a14011ff2e5a750a008ff972d42650047fcb969d328023fe5cb48994015fb2e5724ca00977d76d212f444bdebb68c90a230fedcd54c390fa776ceaa61c87a3fb735530e43d9ddb3aa98721f4fcd0140c390f6776cca9a2277b3bb66505113bd9edb2282889de9eed9953444ef3776ceaa61e77abdb654cceec353bdb42a6885da3deda153442ed6af6d0a7a2266b5bb6650511335aedb22828899a76ed9d54c3ccd63faed8721e668fbb6755330ba5b9db328288912dd6d9141444893e76ceaa61e44b37d76c390f224ebebb698879127d6d9554c3489e2f61c8799a44f17d113bccd22799d875d18350ede6d9141444671f7aeca961e33c7b9534430f19cfcdb2aa9868ce3ee5cb50bb4675b72e58799a33f1bd113bccd19c7dcb96a1748cebce5cb0f22467e67a227791233f53d113348919fc9e7799a448ce3ee5d33119ae55776cca99dd42b75b6853d11115bcdb32828888a7e6d9d54c3c4567baed8721e22f35b0e43c89115eadb621e4488bcd7444ef224453f32e9878ce22f39d113bc67117b8e88 else 0x72d4286b875bd985d1435c3eceba306a1ae13fe6c2aa5c9708ff972d4284b875bd985d1425c3ed6ba304a12e11ff2e5a84c9708ff972d2264b86dbda45d1325c26fedbd54c02e13ef6d2aa60170cbfb52ba300b853fdb4aa9981c29fed9554cc0e19bfaa99661070afbd76c23263857eebb611921c337f5532cc10e19efaa99460870ef5b64ca3043867deaa64d821c31fe5d330a10e18ffaa99850870e77b68cc2843873edb2661421c337f5532ca10e19bf6a19650870e77b30c22843876bd96611421c33ef55326a10e19f76a19350870ef3b08c9a843873ed98609421c3b76cb304a10e1deb6518250870ef9b26c12843857f6bb611911c2bfb5db04c88e15fdaed4264470afeb70a13223877b584509911c3bf2c1284c88e13f76ceaa61d60cfb95251b0eb047fcba662775823fe5d330ba2c1fa75918350d609f7b6955300b047fdb7aa9985027eed9d54c3a819f72a4a361d40cdfd32d310ea047fcba662775023fe5d30ecb2811ff2ea77659408ff974cbb0ca047fcba66176502f5edb150ba2817ee6c0a85d140eb7972c3ae8a07d9cb361d74502fdcd810eb2281e6f61d7460d408ff974cc2e4a05fb9b4aa980502f7cdb14ec02817ee6d0a760140f7b166c3b00a05fb8ba5d180503edcd3ae8c0281eee61d7460140fb730eba300a07bb9865d180502fdc5d2c8c0281eee61d6460140f3f30eb9b00a079f9875c9805027de5d2e8c0281e6f61d7460140db7b50ba2e0a07db974601705023fedbd54cc2611ff6dca9a21308ffd7654b0e9847fcba61d964c23ff5d952c32611ff6dca9619308ff974cbb0c9847febb2a5764c33deda152bb2613ef6d0a95d9308ff974cc2ec9847fdb7aa9944c23fe5d30eca2611ff2e986651308ff974bb3289847febb2a5744c33eed9952ba2611ff2e5a85d1308ff974cc2e89871fd9861d744c23fe5d32cba261d6f61d945d130bbbb6e4c2e69875dcb961d734c3eecd830eb9a615f72e58758d30bf3b684c2869857dcb9a21434c2bee5cb0ea1a61cf76618750d30dbbb4ec3a869857dcb95d9434c2fce5cb08a1a617e72e57450d30ef3972ba286985f9db85d1434c3bcecc2e8a1a61f6761d7450d30bf3972b228698779d98591434c23ff5d952b92619f76cca95c9308ff972d42e49847fcba661724c38fecc30eb92611ff2e9945c930cfb952a1ae49847fcb96a1424c23fe5cb4ea12615ef2e57450930afb972c3a649873dd9861d324c2bee5cae899261be7691744c930bf736955300985fd9b3aa9804c2dfcdc532c02615fe2e57660130df734e52300987bb987291804c3ddcc3148c0261cfe61d9460130e7f30cca300985bf9b85d1804c3cfcc3ae8c0261dee6517460130ef7328b2300987dd9875cd804c3decc32e6c0261fe62917360130f7b308b9b00985fd8ba58d804c3decc3ac6c02)) else (if i < 5 then (if i < 4 then 0x85d2ededa554c3ae97776ceaa61d74b3fb714cb0eba6ddca3681875d2ededa140c3ae93f76ceaa61d74cff1305032cba6df987281965d27f6d9554c32e91ffaeca961974cdfb6c54b0cba47fdb02a5865d2f7c5832cc32e95bf6d89864d74adfb6c4c320ba63fe996a0905d34fedbb50482e91ff6e89824174c7fb504c120ba69fda861c905d337f4cb4c482e99bf661a624174cdf930d3120ba6cfd87698905d33ef4cb46482e99f7661a324174cfb930d1920ba6ddd8768c905d37ceda346482e98ff6a19324174cdfb4cc9920ba67ee99688905d33f6cc344482e9b7b61da224174cfdb26d1120ba63fda8648905d337ed3324482e99f768d92241749fbb675530eb267dca928d875923fe5d3313bac91ff6c2aa66173bbbb675530eb9ddddb3281875ce7f6d9554c32e73bf2ea885d9638ff974cc2e8b1c7fdb7aa99850e3fed8554cc2871ff6c2aa65d43adfb6c5432ea1d7edb22819750e3fe5d30ecb2873fb6caaa619438ff974cbb0ca1c7fcba6617650ef5edb150ba2877e76cca85d1439f7975442e8a1f5bcb961d7450eddedc140ba2877af6d8a05d143bf3b66502e8a1dfadb22817450f9ee5cb0ec1a87be72e97460d43fb3b0eba306a1df9db75918350fdcec3ac8c1a87fa76196460d43bbbb675530eb94fddb3aa9875ca3fe5cb50a1ae5e7761d8350d729fbb675530ea167dca928d8750b7ced2146c3a851ff2e9989dd42eb7972c3ae8a17d9cb361d7450addedc140ba2857af6d8a05d142bf3b66502e8a179bd875d18350abdeda152c3a651ff2e9985d132e7b972c3b069979dd875d1834cb3de5bb494cb019ef69da4a6580cf7b4cd2532c067bda468e996033ded23454cb015ef6d29925d80cdfd32d312ec057bdb4a66776025fe5d4eec33011ffaeca95d980af7b694caecc056fdb625d94602bdedbd324a3015ef6ce9925180bd7b6c4b928c057bcb99dc94602bde5caec4a3016bf6d897611808ffd7654ae8c063fdb82a57460337edb152ba3015bf6d8a95d180f3b966c3ae8c057bdb4a6573603cdec3928b9b015ef6d29958d80cf79524a2c6c047fcb969d436034fed3b0ea1b01aef2a58450d80af7972ba286c05bbdb85d143603cdec3ae8a1b015bf6d897649808ffd7654ae4c057bdb4a6572603cee59b0eb93019ef2a4945c980f37b0e4a2e4c04fddb32a5426035de54b08a13015ef2e57450980b77b70ba284c079bd875d142602bdeda532993019ef2a4944c980ef3928c9a64c047fdb9aa9742032fed3b2ea1901d6f65d7450c80ef3ae8c9a864063fda82a2995c2b7edb1514cae13ef6d2aa661709fbb6755330b86f9ca428d985c27eed9d54c3ae13fe6c2aa61d708ffd7654b0cb847fcbaa65865c2efcd8554ba2e176f6d2995d170b9fb6c542e8b875dcb3661745c2afe5cd10ba2e13fe6c2aa5d1708ff9 else 0x2768d3449a1ed0c684b4199e8cec674b3859b2cd1664b305968cac654b285932c91647322d910c8563c31d58dac6a633b1918c2c5e62db1618aac4862030cd842c0f606302580cc036002fe17e0bed5f02f25782bbe5d8aeb9756b9e5cb2e39702b745ac2d2d67cb3b594ac71632b115872c2d610b055812bfd5f8af9578abb95ccae35702b615a0acd562ab09574aad552aa89534a8d5452a1d4f4a72537a99d4c8a6152f296d4b0a55529292948ea26511a86d426a10506a8153fa9fa4fba7bd3ce9df4eba73d3989c94e3270d3769b34d826b53549a24caa64931e98c4c4a6193069804bea5e92ee96f4b3a5912c295e4ada5612a09484a024f5260928490246122090348023f51f48e8472a3751aa8cd465231d17e8bc45a22c51528a144f225911c886441a1ed0f087043421810ba85a42ba13d08e83f41920a904e815406a0150047ff3fe1fe4fe27e93f31f78fac7d33e59f0cf807b83da9ec8f5e7a73d21e48f0a7823bd1dc8ede76c3b21d70eb27473a21cdce687313949c70e2870c3849c18dfc6f63771bacdc66e036e9b54d9a6ca35e9aacd4669b3471a04ce86673321984cb2656329992cc9064532118fcc6e6343161890c2e60530117e8bda5ea2ee9740b905c52de96e8b5a5a52d1167cb2e5942c89610b025792b895b8ad65632b01560aaa54d2a5151ca8854129c94d8a5c52628f1458a1250127793749a04c825d92cc9564a324d926091647e23d91e08ea47223791b08d246623191808ba45a22b91508a2449223110c88043d21d10c885e42c214909884641b209902c8063f61f98fc07da3e51f10f547a43cf1e38f107823b91db0ecc72438f1c10dfc6ee36f1b60da46c235e1ad8d606aa34d1a28d0867e33719a0cc465c32b1940c9464431f18e0c506182f51790bbc5d82e91730b785b62d31658b2058a2c215f8af05722b61598ac055a2aa1538a9054229e14d8a6052a2921478a305122861418a004fa27a13b89d04e226e13589a04b624e125890c47623811a88c845e22c114889844622010e886842e214108883841620810288083fe1fc0fc87d83e61f00f687a83ce1e40f087783b61d80ea874839e1cc0e487183861c00dc06d436419b0c705dc2de16c0aa854829e14709804141fa0fa06c83441920c105c82d815c0ab054028013a09a04b825012208e045822010a08203f81f00f207603981c00da06a031017c0b805902b014c0a004d025011c07e032015009c03400d00033ee583474cb0f9f7699a3a6587cfbb48d1d32c3e7dda368a9961f3eed1b414cb0f5f76da9924d87afbb694c926c3d7ddb0a649361ebeed9d324830f9f76989324187cfbb4849920c3c7fdb02a67761abf6d95333bb0d1ff6c0a9a21769f7b6854d10bb4fddb3aa9875da3fed8554cc2e99f728ca066174cdfd32d3130ba47fdb02a68) else (if i < 6 then 0x830583040000000000000304002810383040404083830783058307830703840810132204090306047082e0810000006098042836081008a068a078287828782051e8602e0a10303851e05c00400000308d022834104000000000000c92202d101014010814f03440c14f03440c080080045210101801e91222364922004108886051744080021ed0824781478187b42881e9122c788d924880105478880a18478201435090a0f1e9082000804000000000000000400281000c101d10100000400121410440800040010141044080014a2122000100040400000000005281001451d445094012a601420544040024206420400142064406440444064404000000c204c4040000034141044080000000000000030904040408000006101e10161018014a102a101f00181013341052840800001368901030004048407c0040000304000c1000406140400241f00100c10012040440100e10121800800307030703070800c200c10089c20030c89844a84000000038404860c0c10101004c0403040178100000080602270800c3178890a052a1e0c1000052160c18114717830e04500a0a0810a8614428220c13341800052133418521005e86081140483060175140a5eb16830c5e045e044a20c22585e0a5e92821789608000440400383040800000304000e1450180c83085d452030e000c132a038a0716830a0320c200010044040c338b8b85040034104003850082008c048c0400004060616180090400000008040e141e161e081e0a187b820908851e423820f1e134080d1e02024781c7a820a8c068c07850400040e14440b8510c20000000000000000000000188040000820440100000003c00780074007c007c1f0020000380060f07c008003800600380040002047819a1303f1a603c1f0020380040d0400011040000000c07c00400380060000000000000d001d001253c1f0344900800000d001001e0740040820800020800800000000000800000800000000800000000f07c00bc1f00200120411040000000000000000000000000000000000000000000000020800800020000034102047817a13c193c1f002f0bc1f0214901106024f4af06109008014045e04283f0640845e0651431283f07c0a01406006514b28c4a0fc69b400740040c07400400781000e001800000000000000000000000000f00100000000000003c007c1f002e0010110f1a2023c68910f1a2f24790bc79e36f1878abc49e1ef077823c05dfcef67773baddd0ee576ebb69daeed47663b25d82ebe75dbaa5d42e9e74dba61d20e88742ba09cfee777303939c8ce4371db8a5c42e1e70b3811bf8df46f8b7b9bd6de36edb761baadd26e7b731b92dc66e1b6edb66db06d6b6a9b4eda46d0b679b36d936c83621b0ad7d6bab5c9aded676afb55da9ed476a234f1a5ed else 0x200000000000309040000d04101410000013040000e1010284040000d701840d840400000101d0810000184040d02000010405284b003a10101c3040d701840d8404030c10518470036101240100001c3058404082000000001)))
def layer511r9 : Packing := (638,4,6,63,0,13,1,packed511r9)
def keys511k10 (i : Nat) : Nat := (if i < 1 then 0xc3500003530ded964e57fb3ffd63a7681f731a0549945664926b223e451b591000062b00024f79271929920816dd67d861a28f94f44978f1b7fd9f04506c1df114885b309d79a9ad0ad45e884a85538e704af20d0003969000109891e39f4f8b00b7774ce7dc6f9c3608d648eb2a11ea90c400010d0261000259595290ee82f0000169211fe85f9a83712180709a981340800055e092a703c000419b2157767daf6124c42265ce5de1faa10b52102f1418c205420970c5cf457f77d459b9f0959d886a4832ac000069c11600009cb63cce4121a8185e01380979ee202c74260f0001c9f2996c44d6cbca22781808c8bc82344ed0e824b2d64a99195e13695b354fc000f4d9a29d6fd8fb8620d2f595fd94963250d05434b1e1ebc9253d9ca6e54dd0c0072104224fca767462604958c0043e887d69c94b6629288c1750de105108070002046724510e76865bc62138a1e880000e46b267f34320a334d0d788ea5bb915b208e75b51c25d610169c523ce16edc0d816ddc9793535848087c092f55bb3c09abf62ee5f11aecc833e603731821c94682600c27a583425185cd39252ed71618286bb035086f028552d66a7121ccb406300c33f6e6337f814758ff43cb5a986e25dac64844f05e488cd96c3fb1c7b242a01a8d155a06b7676d38a4c120e002940f8e74d679cbb44e60de0000e69067005300021e900ec0000000a2a00034b3c2bd13871fc552878c12df428000a168000c11f9459859e12802d8f867795670177213c82f830d73400a749d51784f69a60003a5100000000001d0700000000000e471006128723edcca0aecc6750f59b00b8000c860cf424f203d72c9958f1be1aa12b8e09000322d14c594d000216875f8cfc72e707788cc0a968b861f25ec97275815f664924c003360a5491312158ca0ef208587b31ce052c7cb5c2e08bd0582b0c6554240d5670e5bae8ef64cb99a44c757c4e5c903dec33aac6c761a237b8f7a0768305fa663b5a56162416f9781ee29b844d10e7e1ca31dc5f6467cbe17e41eb60a8c3a2451222e73a13e432acdc0002032668f81e69618c92853e4285f0d3a04479dda2838c33599dbd45b29fb0875d90296d40e52d0a0e419f406404e9039989097c2180ec1f040000120e0104000001060100010e140d150000000102030f0033080602072102011100251101032202050307040b000601070008030a002d1100000601483500031d241404060b04000e212a0231cc0701417d02009312090004005a0305000a111f4a032304000a00020501010a1803047430081400010a1605040e05260001350002020001120d0000070900000502030700270108110633023c0f4a08080f20000731002102020602270b45050502200ba6025a29092603000001000a0c0000000100200e003015010600000d19160300 else 0xc570ce99476e55426c0c5c04a08d40534bf52eb63100022388311caab488869975d4ce19171f1681b03f522904be7cc962000316ec0549c8937c8db53ac4dd24dcc1089419c6f966c27f0b2c755509d71687b6784546273e9710b8874a2198266d34d7d602d026bd9ab89eddb56c158718680000000c6da2d4000547808173b41d5218c00000001008256a26a38dc708258888439a67700021e76594961b5bf0cc6689526004400036c70bde63dc7190370cf0000000000f9555460000993ba4a953898d36240000000000a93c000042f59800034d1206e5cff676a79434a9ca0003c74713c02536a51564366ce065740000000000b7048d6b78b912000316b58e59efa10400096e150fc154000a07ea6c6501e7a13cb08b00005fd0895130695000083d5a6d5812d5700021f886dd0804629889d936de88968843e274000436000097994540003243a610000e188000b138000000000018445b5a384000000011000000009762433e91981a27f045100009e5d05c00051e7275f008000e064d7da4cc000c8c311b41dba707890c8758dad77e09225300000000000d7401caa68548c000000293236d0000000280536e5840f66726f91431b6064aa03d8a34837948000e2c0000)
def packed511r10 (i : Nat) : Nat := (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0x3fda335ca00bfeaa942802ff8a950a00bfe6a142803bfa8850a00bfe69d42803dfa7750a00fee61142803fb97450a00ff68cd42803fe98250a00bfeaa932802ff8a94ca00bfe6a132803bfa884ca00bfe69d32803dfa774ca00bfe69132803fba444ca00ff660d32803fe9824ca00ffa5c932803fe89888a00ffaa2222803fe89788a00ffa61e22803fe88788a00ffa9de22803fe98488a00ffa5d222803fe98388a00ffa5ce22803fe94388a00cff2a6888027fca9a22009ff2a5878039fd8721e00bfe680878035fca99de00e7fa22778027fca99de00ebfa2266803cfe7799a009ff2a574803bbe8891200f6f9de44803ebe6691200ef7a2233803dde778ce00fb799a33803f9e448ce009ff2a572803bee8888a00f7b9de22803fae4488a00ff38ce22802ffaaa60200efea2180803bf98760200f7e9dd80803efa6660200fee29180803bf98460200fee91180803fda3360200ffa88980802ffaaa5c200bfe6a170803bfa885c200f7e9dd70803efa665c200f7e5d170803fba445c200ff68cd70803fea225c200efea2160803dfa7758200fee91160803fda3358200bfe6a140803bfa8850200bfe69d40803dfa7750200fbe99940803fb97450200ff68cd40803fea2250200bfe6a130803bfa884c200bfe69d30803dfa774c200fbe99930802ff9a44c200fee91130803fd9734c200ff650d30803fd9324c200ffa88930802ff9a848200efea2120802ff9a748200f7e9dd20802ff9a448200fee91120802ff9a348200ff68cd20803fe97248200ffa50920803fe93248200aef69097a22bdda324288afb68890a227dda3a6587a7faa98721e6feaa658879fb68a9961b8fd8721e66e3fa227799b9bd8721e44baf698879139be889de44eafa2266913cbe7799a449f72a5878cf9de889de33eb7a22668cfcde7799a33ee7a22448cfd9e7791233fa799a448cf9ed8721e22bbb6988788b9ee889de22eeba224488bdae7791222ef3a223388bdce778ce22fe39123388a7bda4a65809ef2a644602bfaaa60080e7e9dd80203afa6660080eee291802033f99460080eee91180203bda3360080efa889802023feaa660709bfaa9961c32fe8865870cbf662661c27beaa65070cefa21941c36be6665070cef662441c36bd9691070cf7a21931c36de6664c70de7911931c27eeaa64870cfba21921c36ee6664870deb911921c33ed9888870dbb65a221c37ad9488870df364e221c33f68864470dbd999911c37b64464470df9889911c2dfaaa5c070e7ea21701c3cfa665c070f6e911701c3dea225c0709bf69a99482ef9a626200e7e61c87802ef9a621e00e7ea2277803afa8899a00f3e9de66803bba8891200f6e9de44803eba6691200ef6a2233803dda778ce00fb699a33803f9a448ce00efaa2222803dea7788a00fea91222803fca3388a00 else 0xdf7a65324c37dd984c930ef7a21324c2fdda74c930f779dd324c2fdda44c930fe7911324c3fcd824c930ff35c9324c37ee9988930dfb662224c3bee8888930dfb65e224c3dee7788930dfb652224c3fae4488930ff35ce224c3fcd4388930bfeaa9804c37fa9960130efe261804c3bfa8860130efe61d804c3dfa7760130efe619804c3efa6660130fee291804c37f99460130efe611804c3fba4460130ff65cd804c3fd96360130ff650d804c3fd93260130ffa889804c2ffaaa5c130dfea65704c2ff9a85c130efea21704c3df9765c130fbe999704c3df9745c130fee911704c3fd9635c130ff650d704c3fd9325c130ffa889704c27fda7a65209ff692994827fda3a6520bef690974827fca961d20d7f2a6774835fe999dd20d7f662774839fe889dd209ff2a6774835fd979dd20d7f9dd944827fca95d120def651744837be9991120def66244483bbe8891120def65e44483dbe7791120d7f9dd934837be4464d20df7a66334837dd988cd20ef7a22334837dd978cd20f779de334837dd948cd20fe791233483dee775c920feb91172483fce335c920f7b9dd42483fad7450920ff38cd42483dee774c920feb91132482ffaaa60120efe61d80483dfa7760120fee29180483bf98460120fee91180483fda3360120ff34c930482ff9a726200bfe69098802ff9a326200bfe68898803bf8a9a2200efe29e88802ff9a825e00efea2097802ff9a425e00bfe68897802ffaaa61e00bfe2a587803bf89861e00efea2187803fd8a361e00bfe69087802ff9a221e00f7e2a677803df8a89de00f7e26277803dfa889de00efea2277803df9879de00efea2186803dfa7761a00efea2176803dfa775da00fbe26266803efa8899a00fbe25e66803ef98799a00fbe21e66803efa7799a00bfeaa984802ff8a961200efe26184803bfa8861200f7e9dd84803efa6661200bfeaa974802ff8a95d200bfe6a174803bfa885d200f7e25d74803df9875d200f7e9dd74803efa665d200efea2164803dfa7759200fee26244803fba8891200fee25e44803fb98791200fee21e44803fba7791200fee61a44803fb97691200bfeaa983802ff8a960e00efea2183803bf98760e00f7e9dd83803efa6660e00fee91183802ff9a85ce00efea2173803df9875ce00fbe99973803fba445ce00efea2163803dfa7758e00fee91163802ffaaa50e00bfe2a543802ff9a850e00efea2143802ff9a750e00f7e9dd43803efa6650e00fee61143803fb97450e00fee59143803fd98350e00ff626233803fda888ce00ff661e33803fd9868ce00ff65da33803fd9848ce00ff65d233803fd9648ce00bfeaa982802ff8a960a00efea2182803dfa7760a00fee91182803fda3360a00bfeaa972802ff8a95ca00bfe6a172803bfa885ca00f7e61d72803dfa775ca00fee9117280) else (if i < 3 then 0xc36fe66650709ff6a5841c33fd9861070dbf659841c37bd9461070def662441c3bbe8891070def65a441c3ebe6691070df7a21931c37dd8464c70dfb611921c37be4464870cff661821c36fd9660870def651821c37dd9360870cff661421c36fd9650870def651421c37dd9350870dfb662221c3bee8888870dfb652221c3fae4488870dfda21911c37f58464470dfd609911c37f54264470f7eaa9701c3df9a85c070f7e2a1701c3dfa885c070f7e691701c3df9845c070f7e689701c3df9825c070f7e509701c33fca9a2160cffa66885833fd98a2160cffa21975839fd8721d60d7f2a6775835fe999dd60d7f662775839fe889dd60d7f65e77583afe885d960f3f9dd76583afe8859160f3f9dd645837be9991160def66244583bbe8891160def65e44583dbe7791160faf5da44583ebd6450d60df7a66335837dd988cd60ef7a22335837dd978cd60f779de33583edd768cd60fb759233583f9e448cd609ffaa9985033fca9a2140cffa6688503bf8a0a2140cff662885027feaa65d40cffa21975027fda961d409ff6a4875039fd8721d40bbf69887502fbda421d40bfe680875035fca99dd40d7fa66775035fd989dd40e7fa22775035fd979dd40cffa21965035fe7765940dbfa66665036fd9899940ebfa22665036fd9799940f3f9de66502fbeaa5d140defa6574503bbe885d140f6f61d74503dbe775d140faf99974503fb8a05d140defa6564503bbe8859140f6f9dd645037de998cd40df766233503bde888cd40df765e33503dde778cd40df765a33503ede668cd40fe75d233503f9d648cd40dfba66225037ed9888940efba22225037ed9788940f7b9de22503fad7488940ff38ce22502ffaaa60140dfea6580503bfa8860140efe61d80503dfa7760140efe61980503efa6660140fee5d180503fb96460140ff68cd80503fea2260140f6f5d1705027fda8a65309ff69e994c27fda4a65309ffaa9984c37bca466130cff660984c33fca9a2130cffa66884c3bf8a0a21309ff2a6884c33fd98a21309ffaa9974c33fe8865d309ff6a5874c27fca961d30cff661874c35fe999dd30d7f662774c39fe889dd30cffa21964c35fe77659309ff2a5864c27fca95d930dbfa66664c36fd9899930ebfa22664c36fd9799930f3f9de664c27feaa65130cffa21944c35fe7765130dbf999944c27fda9611309ff6a5744c27fca95d130def651744c37bd9459130defa66444c37bd9891130eefa22444c37bd9791130f6f9de444c37bd9691130faf99a444c37de995cd30ef7a21734c3ddd875cd30fb7999734c3f9e445cd30df7a65634c3bde8858d30f779dd634c3f9e4458d30bf7aa9434c37de9950d30df7661434c3bde8850d30bf769d434c3dde7750d30fb7999434c3f9d8450d30fe75d1434c3f9d6450d309ff2a5724c2fdeaa4c93 else (if i < 4 then 0x22f7b61d7388bfae445ce22bfbaa94388afeda850e22efba214388afeda750e22f7b9dd4388bfad8450e22feb5d14388bfcd8350e22ff3a223388bfcd878ce22ff36123388bfcd748ce229ff69e996027fda4a6580def692996027fda3a6580bef692996035fd9725d80bbf69897602bfeaa61d80cffa65876039fc9761d80ef728d87603bf8a061d80d7f2a6776035fe999dd80e7f2a2776039fe889dd809ff2a6776039fd879dd80cffa65866039fe77619809ff2a5766036fe9999980ebfa2266603afd8799980f3f9de666037be9925180eefa20946037bd9725180def25c94603bbd8725180f6f9dc946037bd9625180eef61894603ebe6625180affaa9846033fe9961180e7f9dd84603afe66611809ff2a574602bfda85d180e7f61d74602fbca991180defa6644603bbe8891180eef61e44603dbe7791180eef61a44603ebe6691180def251936039fd875cd80eef611436037de998cd80ef7a2233603bdd878cd80f779de33603bdd868cd80fb799a33603f9c948cd80ef761233603f9e448cd80def251926027fca95c980e7f61d72603bbd8450980dfba6622603bee8888980efb61e22603dee7788980feb25222603bed8488980feb91222603fce33889809ffaa9972035fd979dc80d7f9dd962036fd9799880f3f9de662035fe7765080dbf999942027fda95d080d7f65d742037bd945d080def65e44203dbe7791080def65a44203ebe6691080d7f9dd932036fe6664c80def911932027fda95cc80d7f65d732037dd935cc809ff6a5432037bd9450c80df764d432037dd978cc80f779de332037dd968cc80fb799a332037dd948cc80fe7912332035fe7764880def911922037de3364880dfb65e22203dee7788880dfb65222203fae4488880dfb64e22203fce3388880efeaa980203bf9a760080efe29d80203bfa7760080efe69180203bf97460080efe68d80203bf97360080efe50d802027fda8a65709ff692995c27fda3a65709ffaa9985c37bca466170df728d985c33fd9826170cff2a6885c33fe99a21709ff2a6885c33fd98a2170d7f662775c39fe889dd709ff2a5865c35fe995d970e7fa21765c36fe9999970dbf662665c3afe8899970f3f9de665c2dfeaa5d170d7fa65745c35fd985d170e7fa21745c3cfe665d170f7e281745c37be9991170def662445c3bbe8891170f6f9de445c3dbd7691170faf99a445c3dbd7450d70df7a66335c37dd988cd70ef7a22335c3ddd768cd70fb799a335c3ddd748cd70fe7912335c3dbd7450970dfba66225c37ed9888970efba22225c3dee7788970f7b5d2225c3fae4488970ff38ce225c27fda960170cffaa9981c33fda466070cff689981c27feaa66070cff662881c36fe8865870cffa21961c36fd9899870ebfa22661c37bda865070defa21941c37bda265070cffa21941 else 0x58f3fe99a2163cff6628858f3fe8865d63d7fa667758f5fd989dd63e7fa227758fafe8861963f3f9dd8658fafe885d963defa664458f7bd9891163eefa224458f7bd9791163f6f9de4458febd8691163faf5da4458e7feaa66143cff2a68850f3fe99a2143cff6628850e7feaa65d43cffa219750e7fda961d43d7f65d8750f5fe999dd43d7f6627750f9fe889dd43cffa219650f5fe7765943dbfa666650f6fd9899943ebfa226650f6fd9799943f3f9de6650efbeaa61143defa658450fbbe8861143f6f9dd8450febe6661143befaa97450f7be995d143bef6a17450fbbe885d143f6f61d7450febe665d143befaa96450f7be9959143bef6a16450fbbe8859143bef69d6450fdbe7759143faf6196450efdeaa60d43df7a658350fbde8860d43ef761d8350fdde7760d43fb79998350ff9d8460d43fe75d18350ff9d6460d43aff2a19250fbdca0a2233bf7aa9878cf7dca961e33ef7a21878cfdde889de33bf7aa9868cfbde8861a33f779dd868cefdeaa5da33bf76a1768cfbde885da33fb7619768cfede8899a33fb761e668cefdeaa61233ef7a21848cfdde7761233fb7999848cefdeaa5d233bf76a1748cfbde885d233f7761d748cfede665d233bf7aa9648cefdda859233ef7a21648cefdda759233f779dd648cfedd8659233fe7a22448cff9d8791233fe761a448cff9d7691233d7f2a67760b5fe999dd82e7fa227760b7be9991182eefa224460bdbe7791182df7a663360bbde888cd82f779de3360bf9e448cd829ff692995ca7fda3a65729ff682995cadfeaa61d72f7728d875cb5fd989dd72e7fa22775cb7be9991172def662445cbbbe8891172f6f61e445cbdbe7791172e7f61d835cb7de998cd72df7662335cbbde888cd72f7761e335cbf9e448cd72bf768c905cb5fca99dd42d7fa667750b5fd989dd42e7fa227750b5fd979dd42befaa98450bdbe7761142befaa97450b7be995d142bef6a17450bbbe885d142f6f61d7450bdbe775d142df7a663350b7dd988cd42ef7a223350b7dd978cd42f779de3350bf9d848cd42fe75d23350bdee7760942feb5d18250bfce3360942d7fa66774cb5fd989dd32e7fa22774cb5fe7765132def651744cb7be9991132def662444cbbbe8891132def65e444cbdbe7791132bf7aa9834cbbdd8760d32f779dd834cbf9e4460d32f7b9dd824cbfae4460932feb911724cbbeca7a2222efb2828888afeeaa61e22efba218788bfcca361e22bfb6908788afeda021e22f7b2a27788bdee889de22f7b2827788bbee889de22f7b61e7788afeeaa61222efba218488bdee7761222bfbaa97488afeda85d222efba217488bded875d222f7b9dd7488bfae8891222feb61e4488bfac8791222feb9de4488afeeaa60e22efba218388bbed8760e22f7b9dd8388bfae4460e22bfb6a17388bbee885ce))) else (if i < 8 then (if i < 6 then 0xe00bffaa943802ffda850e00bff69d43803fbd8450e00fef5d143803fdd8350e00bffaa982802ffeaa5ca00dff2a572802ffda85ca00f7f61d72802ffeaa50a00bff6a142802ffda750a00fef61142803fbd7450a00ffb60942802ffeaa4ca00bff6a132802ffda74ca00bff69132803fdd834ca00ffb60932803fed724ca00aff69897a22bfda425e88aff68097a22bfda724288aff69890a22bfda424288aff68c90a227fda4a65879ff68e9961f7dda3a65879ff6829961efdda3a6587df7a649361fbde8824d87df76589361f7dd9424d87df724d9261f7dc9364187df724c9061f7f99024187e7faa98721f9fda661c87e7f6918721f9fda061c87e7f2818721e7feaa64087b7f698989dedfda426277b7f688989dedfda026277e7f2a6889df9fca0a2277b7f6a0909df9fe8824277b7f698909dedfda424277b7f688909df3fca9a22779ff2a6889dedfeaa61e77e7fa21879de7fda7a65869ff6929961a7fda3a6586d7f2a67761b5fe999dd86e7fa227761a7fca99dd869ff6a2995da7fda4a65769ff68e995db3fca9a2176cffa66885da7fca9a2176cff662885db5fd989dd76e7fa22775dbafe8861976f3f9dd865dbafca7a2266ebf2828899aefeaa61e66ebfa218799bedca361e66bbf6908799aefda021e66f3f2a27799bcfe889de66f3f2827799bafe889de66f3f61e7799b5fca99dd84d7fa66776139fe889dd84dbfa6666613afe8899984f3f9de666127fda8a65749ff68e995d27fda0a65749ffaa9985d37dca366174cff660985d2efda626174cff2a6885d33fe99a2174e7f29e885d27fca9a2174cff662885d2dfeaa61d74d7fa65875d39fc9861d74e7fa21875d3ddca361d74d7f662775d39fe889dd74bfe281965d27fca961974dbfa66665d36fd9899974ebfa22665d3cfd8799974f3f9de665d2bfda824174bbf698905d2fdda324174bfb688905d37f99024174cff2a6885933fe99a2164cff662885933fe8865d64e7f61c875935fca99dd64d7fa66775935fd989dd64e7fa22775935fd979dd64ebfa2186593cfe7761964eef29e88913bbca0a2244befaa987913bbe8861e44fe728d87912fbda621e44bef68887912fbda021e44f6f2a277913dbe889de44f6f28277913bbe889de44f6f61e77912fbeaa61a44eefa2186913dbe7761a44befaa976912fbda85da44eefa2176913dbe775da44faf61976913ebe8899a44faf61e66913ebc8799a44faf9de66912bfeaa61d83cffa658760f5fe999dd83e7fa227760f6fe9999983ebfa226660fafd8799983f3f9de6660f9fd875d183defa664460fbbe8891183eef61e4460fdbe7791183faf99a4460e7feaa66173cff662885cedfeaa61d73e7fa21875cf6fd9899973ebfa22665cfcfd8799973def662445cfbbe8891173f6f61e445cfebe6691173cff2a688 else (if i < 7 then 0x24c3fdd435c930ffb649724c2ffeaa50930bff2a5424c37fe9950930bff6a1424c37fd9850930bff69d424c37fd9750930fef611424c3fbd7450930ff75cd424c3fed8250930ff761d324c3fdd844c930ff75d1324c3ffaaa60130ffea65804c3ff9a760130ffe65d804c3ff98760130ffe699804c3ff99660130ffe619804c3ff97660130ffe691804c3ff99460130ffe611804c3ff97460130ffe591804c3ff9a260130ffe649804c3ff98260130ffe5c9804c3ff94260130bffaa9804c37fe9960130dff65d804c3bfd8760130fef291804c37fd9460130eff611804c3fdd7360130ff750d804c3fdd3260130ffeaa9704c3ffa995c130ffe6a1704c3ff8a85c130ffe661704c3ff8985c130ffea21704c3ff9a65c130ffe659704c3ff9865c130ffe691704c3ff9945c130ffe611704c3ff9645c130ffe689704c3ff9925c130ffe609704c3ff9425c130bffaa9704c37fe995c130bff6a1704c37fd985c130dff651704c3dfd745c130ff750d704c3fdd325c130ffe601704c37fe9958130dff661604c37fd9758130dff651604c3fdd7358130ff750d604c3ff98058130ffe5c1604c37fe9950130bff6a1404c37fd9850130bff69d404c37fd9750130fef5d1404c3fdd7350130ff74c9404c3ff98050130ffe5c1404c2ffda425d20bffaa9874837fca961d20ff728d87482ffca99dd20dffa66774837fd989dd20dff9dd94482ffeaa61120bffaa974482ffca95d120dff2a5744837fe995d120bff6a1744837fd985d120dff65d74483dfd875d120ffb68974483ff8a05d120dff5d193482ffeaa60d20eff61d834837fe995cd20bff6a1734837fd985cd20f7f61d734837fd945cd20bffaa943482ffca950d20dffa6543482ffda850d20dff66143482ffda750d20dff65d43483fbd8450d20fef5d143483fdd8350d20ffb68943483fed745c920ffb50d72483fee7750920ffb5cd42483fed744c920ffeaa980483ff9a760120ffe29d80483ffa7760120ffe69180483ff97460120ffe68d80483ff97360120ffe50d80482ffeaa60120eff61d80483fbca460120eff61180482ffeaa5c120dffa6570482ffda85c120dff661704837fd945c120f7f5d1704837fd935c120ffb5c970483fed425c120ffb4c970483ff9805c120dffa6540482ffda850120dff66140482ffda750120dff65d40483fbd7450120dff64d40483fed7250120ffb4c940483ff98050120bffaa9304837fe994c120bff6a1304837fd984c120bff69d304837fd974c120bff691304837fd944c120ff75cd30483fdd434c120ffb5c930483fed424c120ffe60130483ff9704c120bffaa9878037fca961e00ff728d87802ffda421e00bff68887802ffeaa61200bffaa9748037fca95d200bff6a174803dfd875d200bffaa983803bfd8760e00bff6a173803dfd875c else 0xc160bff6a170583dfd745c160dff29d985037fe99a2140dff2a1975037fe8865d40bffaa9875037fca961d40dffa65875037fd9761d40ff728d875037fe9921d40bff68887502ffda021d40dffa66775037fd989dd40dffa21965037fd8765940dff21d965037fe7765940dffa65865037fd9761940dffa65765037fd985d940dff65d76503fbca85d140fefa2174503fbd875d140fef61974503fbd765d140fefa2164503fbd8759140fef21d64503fbe7759140bffaa9835037fe9960d40dff65d83503bfd8760d40dff65983503fbd7460d40fef591835037fe995cd40bff6a1735037fd985cd40f7f61d735037fd965cd40fef591735037fe9958d40dff661635037fd9758d40fef5d163502ffeaa60940dffa65825037fd9760940fef5d182502ffeaa5c940dff2a5725037fe995c940bff6a1725037fd985c940dff65d72503dfd875c940fef5d172502ffeaa4c940dffa6532502ffda84c940dff66132502ffda74c940dff65d32503fbd744c940ff760d32503fed824c940ffb5c932503ffaaa60140ffe69d80503ff8a760140ffe65d80503ff98760140ffe9dd80503ff9a660140ffe65980503ff98660140ffe5d980503ff9a360140ffe64d80503ff98360140ffe5cd80503ff96360140ffe68980503ff99260140ffe60980503ff97260140ffe4c980502ffeaa60140dff65d80503bfd8760140fef5d180502ffeaa5c140bff6a1705037fd985c140fef5d170503ff9805c140dff661605037fd9758140fef5d160503ff98058140dff6a2994c37fda7a6530dff69a994c37fda4a6530dff68a994c2ffda8a6530bff69e994c2ffda4a6530bff68a994c37fe9926130bff69c984c2ffda426130bff688984c2ffca9a2130dffa66884c37fca865d30dffa21974c37fc9865d30bffaa9874c2ffca961d30dff2a5874c37fe9961d30eff661874c3ff9a061d30dffa21964c37fd8765930dff261964c2ffca961930dffa65864c37fd9761930bff2a5764c37fe995d930dff661764c37fca865130dffa21944c37fd8765130dff619944c37fd7665130dff261944c2ffeaa61130bff2a5844c37fe9961130dff65d844c37fd9661130bffaa9744c2ffca95d130dff2a5744c37fe995d130bff6a1744c37fd985d130f7f61d744c37fd965d130fef651744c3fdda35d130bff2a5644c37fe9959130dff661644c37fd9759130fef651644c3fdc985cd30ff7a21734c3fdd865cd30ff7611734c3fdd645cd30ff7261634c3fde8858d30ff761d634c3fdd8458d30ff75d1634c3fdc9850d30ff7a21434c3fdd8750d30ff7619434c3fdd7650d30bffaa9824c2ffca960930dffa65824c37fd9760930dff651824c3fdd7360930ff750d824c2ffeaa5c930bff2a5724c37fca95c930dffa65724c2ffda85c930dff661724c3dfd875c930dff6517)) else (if i < 9 then 0x985c3fbca466170ff728d985c37fe9926170bff690985c2ffda326170bff688985c2ffca9a2170dffa66885c2ffeaa61d70dffa65875c37fe9965970dff661965c37fc9865970bff2a5865c37fe9961970f7fa65765c3dfd985d970f7f261765c3dfe885d970dffa65765c37fd985d970f7f61d765c2ffeaa65170dffa65945c37fd9865170dff261945c37fd9665170f7f5d9945c2ffeaa61170bff6a5845c2ffca961170dffa65845c3dfd7661170f7faa9745c3dfe995d170f7f6a1745c3dfca85d170f7f661745c3dfc985d170f7fa21745c3dfda65d170f7f659745c3dfd865d170f7f68d745c3dfda25d170bffaa9745c37fe995d170bff6a1745c37fd985d170f7f61d745c3dfd765d170bff2a5645c37fe9959170dff661645c2ffeaa64d70dffa65935c37fd9864d70dff261935c37fd9664d70f7f5d9935c37fd9464d70f7f5d1935c2ffeaa60d70bff6a5835c2ffca960d70dffa65835c3dfd7660d70f7f5d1835c2ffca958d70dffa65635c37fd9858d70f7f5d1635c2ffeaa50d70bff6a5435c2ffca950d70dffa65435c2ffda850d70dff661435c3dfd7650d70fef611435c3fbd6450d70ff760d435c2ffeaa64970dffa65925c37fd9864970dff651925c3dfd7464970dff64d925c2ffeaa60970bff6a5825c2ffca960970dffa65825c3dfd7460970bffaa9725c37fe995c970bff6a1725c37fd985c970f7f61d725c3dfd745c970bffaa9425c2ffda950970bff2a5425c37fe9950970bff6a1425c37fd9850970bff69d425c3fbd8450970fef5d1425c3fed8250970bffaa9325c2ffda94c970bff2a5325c37fe994c970bff6a1325c37fd984c970bff691325c3dfd744c970ff760d325c3fed924c970ffb609325c2ffeaa60170dffa65805c2ffda760170eff61d805c3fbca460170eff611805c3dfd7460170dffa21961c37fe8865070bffaa9841c37fd9661070bffaa9821c37fd9460870bffaa9421c2ffda850870dff661421c3fbd8450870ffb609421c37fe99a2160dffa2197582ffeaa61d60dff2a5875837fe9961d60dff65d87583fdca361d60dffa6487582ffda421d60bff680875837fe999dd60dff66277583efe885d960fbf61d76582ffeaa61160dffa65845837fd9761160fbf5d984582ffeaa5d160dff2a5745837fe995d160bff6a1745837fd985d160dff65d74583dfd875d160fbf69974583efd765d160fbfa2164583efd8759160fbf21d64583efe7759160bffaa9835837fe9960d60dff65d83583bfd8760d60fbf5d983583efd6460d60dffa6573582ffda85cd60dff66173583dfd875cd60fbf59173582ffeaa50d60dffa6543582ffda850d60dff66143582ffda750d60dff65d43583efd7650d60fef61143583fbd7450d60ff760d43582ffeaa60160eff61d80583fbca460160eff61180582ffeaa5 else (if i < 10 then 0x61943dffa658650f7fd9761943fbf6598650effeaa5d943dff2a57650f7fe995d943bff6a17650f7fd985d943fbf6197650ffbd8761143fef6198450ffbd7661143fef2a17450ffbe885d143fef6197450ffbca05d143fefa216450ffbd8759143ff761d8350ffdd8660d43ff75d98350f7fe999dd82bffaa97460b7fca95d182dffa657460bdfd875d182dffa657360bdfd875cd82bffaa94360b7fe9950d82bff69d4360bfbd8450d82fef5d14360bfdd8350d82ffb6894360bdfeaa61d72f7f691875cbdfda361d72f7f681875cbdfca061d72bffaa9875caffeaa61172bffaa9745cb7fe995d172bff6a1745cb7fd985d172f7f61d745caffeaa60d72bffaa9435caffca950d72dffa65435caffda850d72dff661435cbdfd8750d72fef611435cbfdd8350d72bff690905caffda324172bffaa98750b7fca961d42fef6918750bfdca361d42dffa667750b7fd989dd42fef9dd8450bfbd875d142fef2817450affeaa60d42eff61d8350bfbd7460d42dffa657350affda85cd42dff6617350bdfd875cd42fef6117350bfee7760942ffb5cd8250affeaa61d32dff2a5874caffeaa61132bffaa9744cb7fca95d132dffa65744caffda85d132dff661744cbdfd875d132ff75d1834cbfed7460932dff69e996037fda6a6580dff692996037fda3a6580dff68a99602ffda7a6580bff69299602ffda3a6580dffa6497602ffda425d80bff2a6776037fe999dd80dff25d96603bfc9761980eff9dd86602ffca95d980dffa6576603bfd875d980dff25d94603fbc9725180fef9dc94603fbd7625180eff25d84603bfe7761180eff5d984602ffeaa5d180bff2a5746037fca95d180dffa6574603bfda85d180f7f65d74603bfd875d180f7f61d74603bfd865d180bff2a5646037fe9959180eff61d646037fe995cd80f7f61d73603bfd865cd80fef25173603bfd845cd80bff2a5636037fe9958d80eff61d63603fbc9458d80eff61163602ffeaa50d80bff2a5436037fe9950d80bff69d43603bfd8750d80eff61943603fbd8450d80fef5d143603fbd6450d80ff764d43603fdd8350d80ffe681436037fc9764980bff2a5726037fe995c980eff61d72603fbc945c980eff61172602ffca950980dffa6542603bfd8750980fef5d142602ffca94c980dffa6532603bfd874c980fef25132603bfd844c980ff764d326037feaa65c80dff691972037fda365c80dff9dd962037fe7765080bffaa9742037fd975d080dff659742037fd7464c80dff659732037fd945cc80bffaa943202ffda750c80dff65d432037fd9650c80fef5d1432037fe7764880dff5d1922037fd7364880dff50d922037fda8a6570dff2a2995c37fda6a6570dff692995c37fda3a6570dff68a995c2ffda8a6570bff692995c2ffda3a6570bff68a995c2ffeaa66170dffa65 else 0x34c22c8228c222c21cc214820a0201c1fbc1f381ed81e541df41cbc1c5c1bfc1b781af41a7019c81968190818841800175816d4162c15a81524147c13f8137412f0124811c410f810500fa80f240e7c0dd40d2c0c840bdc0b100a68099c093c08dc085807f8077406a8062405c4051c04bc045c03d8039c033c02dc02a0024001e001a4014400c0006000037fda6a6587dff6929961f7fda3a6587dff68a9961f7fda0a6587bff69a9961effda4a6587bff68e9961effda0a6587dffa649061effda624187bff6909061f7fd9424187bff68c9061f7fd9324187ff724c9061f7fd9224187dffaa99021f7fda664087dff6919021effda425d86bff2a67761b7fe999dd86bff690985daffda326176bff2a6885db7fe99a2176bffaa9875db7fe9961d76fbf61d865db7fe999dd84bffaa9766137fca95d984dffa6576613efd865d984dff6a2995d37fda6a6574dff68e995d37fda2a6574dff682995d2ffda8a6574bff69a995d2ffda3a6574bff68a995d2ffda0a6574dff281985d37fe9926174bff698985d2ffda326174bff688985d2ffda026174bff2a6885d37fe99a2174f7faa9875d3dfe9961d74f7f699875d3dfda361d74f7f689875d3dfda061d74f7f281875d2ffeaa61d74dffa65875d37fc9865974f7f61d965d2ffeaa61974bff2a5865d37fca961974dffa65865d3dfd8761974fbf659865d2ffeaa5d974dffa65765d2ffda85d974dff661765d3dfd875d974fbf619765d37fc9864d74f7f61d935d3dfd8764974dff261905d3dfd8764174dffa64905d2ffda824174dff660905d37fc9824174f7f61c905d2ffda624174bff68c905d37fd9324174bff688905d37fd9224174dffa66885937fe8865d64bffaa9875937fca961d64dffa65875937fd9761d64ff728d875937fe9921d64bff680875937fe999dd64dff66277593efd8761964fbf9dd86593bfca061d83bffaa97660f7fca95d983dffa657660fefd965d983fbf6197660effeaa5d183dff2a57460f7fe995d183f7f61d7460effeaa59183dffa656460effda759183eff61d6460fefd8659183dff281985cfdfeaa61d73f7f699875cfdfda461d73f7f689875cfdfda061d73f7f281875ceffeaa61973f7f61d865ceffeaa61173f7f61d845ceffeaa59173bff6a1645cf7fd9859173f7f61d645cfefd8659173dffa668858f7fe8865d63bffaa98758f7fca961d63dffa658758fefda661d63fbf61d8658fefe885d963bffaa98458f7fe9961163dff65d8458fefd8661163fbf5d98458effeaa5d163dff2a57458f7fe995d163bff6a17458f7fd985d163f7f61d7458fefd865d163dff2819850f7fe99a2143dff2a19750f7fe8865d43dff2819750effeaa61d43dff2a58750f7fe9961d43f7f65d8750ffbda461d43dffa219650f7fd8765943bffaa98650f7fca9)))) else (if i < 17 then (if i < 14 then (if i < 12 then 0xf48fe34fdf8fd74fd38fcb4fba0fa8cf99cf960f870f7a4f6b4f5e8f51cf450f360f294f258f1d4f198f114efb8ee80ed90eca0ec88ec28ec10ebf8ebbceb80eb20eae4eaa8ea6cea30e9ace970e934e8f8e8bce838e7fce7c0e73ce6dce658e5d4e598e538e4fce4c0e484e400e2ece2b0e22ce1f0e1b4e178e0f4e070e034df20dee4dea8de6cde30dc8cdc50db84da94da58d968d8c0d7f4d7b8d77cd740d704d6c8d68cd650d614d5d8d59cd560d524d4c4d464d3e0d338d2d8d254d23cd1dcd158d0d4d098d05cd020cfe4cfa8cf6ccf30ceacce28cdeccdb0cd74cd38ccfccc78cc3ccbdccb7ccb1cca2cc9a8c8b8c834c6fcc5e8c564c4e0c414c300c15cc048bf34be44be08bdccbd90bd54bc64bc04ba84ba48b97cb844b7c0b784b724b6e8b6acb670b580b448b40cb3acb370b334b2f8b154b118b0dcb0a0afd4af08ad88ace0abf0abb4ab78ab3cab00aac4aa88aa4ca9eca968a878a7f4a770a710a68ca608a584a524a4c4a3f8a374a2a8a224a1a0a0689f9c9e889d509cf09c909ba09b1c9a7499f098dc9858976896c09684962495e895ac9570953494f8947493f093909330931892b89210918c90c0903c8f288e388d248ca08bf88b088a18892888a4884487e487848700865885d4852c84a883b882c881fc8178801c7f087df47d4c7c387bfc7bc07b3c7adc79a4794478e4778876bc7680762075c07560750074a0744074047380732072c07260720071a0714070bc70386f906ec46e1c6d746ccc6c6c6ba06b1c6a50696068dc68586768672c66f066b46678663c65dc657c651c64e064a46468642c63f063b46378633c630062c46288624c623461d46198615c60fc60c060a8604860305fd05f945f345ed45e985e5c5e205e085dcc5d905d545d185cb85c7c5c1c5b985b805b445b085acc5a905a785a1859dc59a0594058e058a45868582c581457905754571856dc56a0566455e055a45568552c54f054b45478543c540053c45388534c5310528c52085184510050c450ac507050104fd44f984f5c4f204ee44ea84e904e544e184ddc4da04d644d044cc84c444c2c4bf04bb44b784b3c4b004ac44a884a4c49c84944490848844848480c47d047944758471c46bc468045fc457844f444b844a04440440443c84368432c42f042b44278423c420040ec3f6c3f543f183edc3ec43d443d2c3d143b943b7c3b643b4c3b343b1c3b043aec3990397839603948393038f43894383437f837bc37803720370836cc3690365435d035b8357c3564350434ec34d434bc34a4348c3474345c3420340833cc33b4339c333c3324330c32ac329432583240322831ec31d43174311430b4309c30182fdc2f7c2f402ee02ea42e442e082da82d242ca02c402be02b5c2a2429c428f827c0273c26b8265825d4257425142490240c23ac2 else (if i < 13 then 0xb8ddac1da3dd9b9d9a1d91dd899d839d7fdd7c1d785d749d70dd6d1d695d67dd641d5e1d5a5d569d52dd515d4d9d4c1d485d371d25dd0b9cfa5ced9ce9dcd89cd4dcd11ccd5cbe5cb85cb25cac5caadca4dc981c921c909c819c705c6c9c669c62dc5a9c591c459c345c231c0f9c0bdc081c045bfe5bf85bf49bf0dbed1be71be35bdd5bd51bca9bc25bbe9bbadbb71bb35baf9babdba81ba45ba2db9f1b991b955b919b8ddb87db841b7bdb781b769b6c1b6a9b66db60db5adb54db4edb4b1b499b45db445b3c1b385b2b9b27db265b1e1b1a5b169b079b03dafddaf7daf41af05ae81ae45ae09ad85ad49ad0dacd1ac71ac35abf9ab99ab5daafdaa79a9f5a9b9a959a91da8e1a8a5a821a79da6ada671a635a5f9a49da461a395a2c9a28da251a215a1d9a19da161a125a0e9a0ada071a0119fb19f519ecd9e499de99d899cbd9c399b919b0d9aad9a4d995d98d997e99765965195f195919531941d93999315920190c98f918e7d8e1d8de18d818d698d518d158cd98c798c3d8bdd8ba18af98ae18aa58a698a518a1589d9899d8961892588a18865882987c9878d872d86f18649863185f585958559851d84e184c9848d8475843983fd83e583a9836d825981457fe97f897ebd7e5d7e457e097da97d6d7ce97cd17c297bed7bb17b757af17ab57a0d79d179957959791d78e1788177fd779d773d762975a574d97479743d740173c57389734d72c9724571c170ad70296fed6fb16f756f156e016dc56d896d4d6d116cd56c756ba96b256aa16a1d6999691568b56855681967dd67a16765672966ed66d56699663965fd65c165a9656d653164d16495641163f963e163a56369630962cd62b5623161f561b9617d614160bd6081604560095fcd5f915f555ed15e4d5dc95db15d755d395cfd5b355a21599d58895775575d5691563155d155b9551154f954bd54815445540952d152715211518d5079503d50014f7d4f414e754e394d494c354b694b2d4a1948e148a5484547e5476146dd455d449143e943ad434d433542b14299421541fd410d40653f093ecd3e913e0d3dd13d4d3d113cd53c513c393b493a35398d3879383d3801377d3741370536813669362d3465342933ed33b13399335d3321320d311d305130152ffd2fc12fa92f6d2f312ef52de12cf12c492b352a692979293d292528e928d12895287d2841280527c9278d27752739272126e526cd26b5265525f525952559251d24bd248124452331221d210920191f291e391e211de51da91c951c111b8d1b751a611a01197d194118bd18a5188d182d17cd176d16e91665162915ed158d1575155d14d914c113ad1371131112d51251121511911155106510290fa50f8d0f750ef10ed90e9d0dad0c990b850a950939080106ed06b1067505f1050103ed02fd02c102850171005cf else 0x42ab3cab346b2e6b286b226b1eab166b12ab0cab046afc2af86af4aaf0eaeaeae2aada6ad22ac9eac3eabdeab7eab42aae2aa82aa22a9c2a91aa8dea8a2a842a7e2a782a6fea69ea63ea5dea57ea4faa49aa43aa3fea3c2a386a326a2a2a242a206a1a6a18ea12ea0cea0b6a0329fae9f729eee9e8e9e529dce9d6e9d0e9cae9c2a9bca9b469ac29a629a2699ea996698be9816976e970e966695e2955e94da947a941a93ba937e931e92be925e91fe919e913e910290a2906690068fa68f468f0a8eaa8e4a8dea8d8a8d2a8d128cb28c2e8bf28bb68b7a8b3e8ade8a5a89fa899a893a88da887a883e880287c6874286e2865e85fe859e84f684728412838e830a82ce826e823281f68196813680b28076803a7fb67f567ed27e967e367dd67d767d167cb67c327bf67bba7b5a7ab27a767a1679da799e796278de783677d6777676f276b6765675d275967536751e74be748273fe739e733e7296723671fa719a713a70fe70c2703e6fba6f5a6ed66e766e3a6db66d566cae6c726c366bd66b9a6b3a6ada6a7a69f66996693668b2685267f267b6677a673e670266a2661e65be655e652264c2641a63726312628e620a616260de607e601e5fbe5f165eb65e0e5dd25d725d365cd65c765c165bb65b325aae5a4e5a12598e592e58ce586e583257d25796571256d65676561655b6557a551a5496543653d6535252ce524a51ea5166510650a65046500a4f864f264ea24e424e064da64d6a4d2e4caa4c024b7e4b1e4ae24aa64a4649c24962490248c648424806478246fe463245ae454e44ee44b2442e43ce436e433242ae420641ca416a410a408640263fa23f423f063ea63e463de63d863d4a3d0e3cae3c2a3bca3b6a3b0a3ace3a6e3a3239d2394e38a63846380a37ce3792375636f636ba367e361e359a34f2346e345633d233963312326a31c2313e309630362fd62f522e862e022da22d422d062cca2c6a2be62b622b022a7e29d6295228ce282627c6276626e2265e25da255624ae2406235e22fe227a221a217220ee20221f9e1f1a1e721dca1d8e1d2e1caa1c4a1bea1b661ae21a8219fe197a18f6184e17a6172216c2163e1602157e14d6145213ce136e130e12ae124e11ca116a112e10ce104a0fc60f420e9a0df20d920d0e0cae0c4e0bca0b460ae60a6209ba091208b20876081607b6075606f60696065a05d6055204f20492045603d20372033602d6022e0186010200a200420005ffa5ff21fec1fe85fe25fd7dfcd5fc51fbf1fbb5fb31fa89fa05f981f921f8e5f8a9f86df831f7f5f7b9f77df669f555f4d1f309f1f5f14df111f021ef31ee41ed51ec61ec49ec0deb89eb29eac9eab1e931e8f5e8b9e87de841e805e7c9e769e72de6f1e6b5e655e619e529e4ede48de331e21de109e0cde091e055df41de2ddd19dc05dbc9d)) else (if i < 15 then 0x187814b810f80d380737fef7f6b7f0b7eab7e6f7e337dd37d737d377cfb7c9b7c5f7c477c2f7bab7b6f7aeb7aaf7a4f7a1379b3795378cf782777a37743772b76a77647760b75cf7593753374f77473741373b3732f72ab726f71c7714370e3705f70236fe76f876f036ea36e1f6de36d836d236cc36c636bdf6b5b6afb6a9b6a3b69db693368d36873681367b3672f66cf664b65c76567650764a7644763e7633f62bb61ef60db60335fd35f4f5e835e235d7b5d1b5c735c135bfb5b775a875a2759a3594358bf583b57b7570f56af564f5613558f552f54ab544b540f53af5373531352b3520b51cf514b513350af504f50134fd74f774f174eb74e574df74dbb4d5b4cd74c774c3b4bb74b574ad34a4f4a13498f495348cf486f480f47af474f471346d74677465f45ff459f451b44df447f4467440743a7432342e7426341df413740d740773ff33f933f0f3eaf3e073d833d473cc33c873c273ba33b673abf3a173993390f388b37e33717364b35a3351f349b341733b7333332d33297323731d73177313b30b730572ff72f972f132eb32e772df32d932d572cd32c4f2bef2b8f2b2f2acf2a6f2a0f29af294f28ef28d72877283b27db277b271b26bb267f261f259b251724db247b23f7239723132223215720f720731fef1f8f1f2f1ecf1e4b1e0f1d8b1d4f1ccb1c231b9f1b3f1b031a7f1a1f19bf198318ff187b183f180317c7178b174f16ef166b15e71563150314c71443137712f3126f123311af110710a710470fc30f630edf0e5b0dd70d2f0cab0c270ba30b430b070a830a4709e70987090308a3084307e30783072306e706ab064b05eb05af057304cb044703c30363032702a3021f01bf011700b7000effaeff06fecafe6afde6fdaafd4afceafc66fbe2fb5efafefa56f9d2f972f8eef88ef852f83af822f79ef71af6def67ef61ef59af53af4daf47af3f6f396f336f2d6f252f1f2f192f132f11af102f0c6f08af04ef012efb2ef2eeeaaee4aee0eed66ed4eed36ecd6ec9aec5eec22ec0aebaaeb4aeac6ea66e9e2e9cae9b2e952e8cee84ae7eae78ae72ae682e5dae59ee53ee4dee4c6e48ae44ee3eee3b2e39ae33ae2fee29ee21ae196e112e0b2e076e016dfb6df7aded2de72de12ddb2dd52dccedc4adba2db42dae2da82d9fed9c2d962d902d8ead8aed872d836d7fad79ad75ed746d6e6d686d626d60ed5aed52ad4eed48ed476d45ed3dad39ed33ed2ded25ad1b2d12ed0ced04acfa2cf42cee2ce82ce22cd9ecd86cd26ccc6cc66cc06cb82cafeca7ac9f6c996c95ac942c8e2c8a6c822c7c2c762c6dec67ec61ec5e2c5a6c546c50ac486c3dec3a2c31ec2bec23ac1dac156c0f6c0bac05ac01ebfbebf3abeb6be0ebdaebd06bc82bbdabb0eba42b99ab916b8b6b856b7f6b7deb75ab6d6b69ab616b5b6b57ab4f6b else (if i < 16 then 0x6c4e30487050240a0401f18223f0f17c68f481208810078be307a7e00382850a84a00785c10413090301404c5f18a0421680141580104c220a048200744e362e9c5c238c094f4b82850b408b0b82090b400b0b820a0ac00a0ac00b050a1509400f0b82090b400b0b82090b400b0b820981080a12c08407096042038461581041383c04442e3d2c230ac0820908c2b020624230ac081890a600408e0f03161e9614c081070a8f719898b9443c1e0313161e9a14c081070a604083a4f1011c645a7a6e003c007800f00144424a604443e00508a005c007800e021e003c0068609401c003800510092414442050780130c1a10345a105450404411420110c0098709158113078015101e003c0040a2034406880f00121e002a20244e0044ac0110302880d101a2028884044300261c2c08583c0098ac2098a0d0c1e002012700430e860d0c1a183800686092b00430e860d0c1a1834306860d0c144038006860e001a18343049580218649c010c322e0086192b00440d1108050858ac2098a0b1016202c406840f00102840d081a103420780090f001508125600841814206840d08144038006840e001a1024ac0108324e00841d08125600881d081e0438006840e001a1024ac0054204958021064ac010c324e00861a2210110c009870b02160f0026202c405860b0c16183c08424110683111c609ce120883418050200c0488e35406001e002004c240d060280a0401718a0500004c220d060280a03012238d50000000000013090441404018338d4ba40000030108228816009215101a203800700440a0a203440700091087800c0040206008810000000000180040c00200180248400044c00406001000c00206009216008816008410045226003a28245c00545048b800a8a09170015141c01242a2e00881d1700430ca1c68891c6883c48e34643c562427c408f2f8d471a211054290a8871a5c56178813e183029c6a317c628478be37063e31422251438d1f1b83152f8d152f8dc18c2210e347c6e0c54be3454be37063e343c6e0c4cbe3458be314230a928a1c69317c6e0c78be3458be37063c5f1a2c5f1b831e2f8d1113158809f0c25cbe35012e34508e34508e3706365c238d1c238cc48c3c140bf1a48471a28471a265c238d1c2221c68c2b108471a4884238d1d2d1090e349108471a3884238d1b2e2108e348884871a3482238d1c2221c68d97088871a4844438d187835088871a50f42221c69035088871a4844438d1d2d1090e34815482238d252d2088e3494b442438d2423810e84c8cb847021d099611c087426465c23810e84cbc68845c68844cbe34423e3442265f1a211f13861e0a71a50a12b8d1f18a110509450e349c6e0c54be3454be37063e343c6e0c4cbe345c6878dc18997c68b8d0d2f8d152f8dc18e97c68a97c68b81c38 else 0x4871a705516849044718243d00145413011d00142c130118218ac4610438cca1c28c56230a1110e34e1462c203d10e34cc0041144a5f1920139a88880aa438d285c2488a5a438d3511114b4871a509a21214be34b4a4405521c6969490a5a238c129a94884852f8d2d0014540b011d0014240b01182410c56230d8507e032890a31588c284c23810ea1890984701970e9995c084c221ccb9a06230e28006202c4058ac209840b081e00385050882a006c0070a0f001c28284415003c283400612c08406c084050860410384302081e141415022c28340070a0a2680880c334aa1a2117c64a4f85050882a0078506800e14144d01101a2280840f0a08842611068338c129f800e101e00340042e1308834180a02e100602e356c0040a0201f182428280a022871824361010f60894142871a6047189412103c0802718a12f001c2034007080d0016002c007080d001c2034007080c2580142180142581080c129e0bf1a460420284b02101c108600508604143843020a1e101a0038406800e101a00384051340440688a02143c2034007080d001c20289a02203c2030a6005046004c082041e0a7078017c24d0a6041030bf07818465852685302081c7828928502383c042501d8570780cb42052785302081c2981040c298a0271a1128240a040112b8c131c2612068301405020089383e3560a0481404c4e304871004c240d0671823384f21c5e171822360c1250383078008481a5e2571827321280104c240d060280a04014438c530010280809c6088a12068300a040171a21404f8d108f060a1280160c16002c00424090252f8c1498261205010294be34428c18284a0058306800e0c10c84c1a0c050240b44c180b8d5b0016002c0041205010478c28280a0208f18509834180a040140544e3442a457042510911508e0f02294b9b060d021c1834007060d001c183086005096042032f4449409e340e684b02101c2581080e10c00a10c0828708604143843020a1c1180142180124c2289e35125843020818409408e3046584302081c2181040cbc93256244294e340e8a501129c6084a1da562510cbe325270984814080252f8d10a204c00a10c008224a44f18bd4b9a10c081061004718bc242181020c9589a5b1011c62f4f086040830fe24944be317a60812f8c5e93060a1280160c1a0038306800e0c144d01101a2280840e14c00a06c00806040c20f05382909214c08187c1e060d96149614c081871e8571783c0c1b1270ca3383c06202a61087829c1e0313073c2981030cbc14e0a42425707801c6585260a707805e0cb1260b12b83c06597a685302061c2580140d80170621142581030f8d8365852484b020618538cc4c1c9096040c30e3298bc10805260c85195c66204260b32b8ccb084b096040c309848220a0200c938be3520a04814))) else (if i < 20 then (if i < 18 then 0x28547b8d8b61ca83a0040608141d002c1028aa020830041c6a187a4c1034087040a2a80820f040f1317c68f49c087040d001c103400614c00a14c08107096005026004124512383c04f62e784b0204186115c6c127a5604082c1034007040d001c1028aa0208344d01041c2981040c3ec8e0f02150b8f4f0a604103c1034007040c2980122a918bc18278c9e9f040d001c1034007040c2980105b8d820807a585302041c2981020e14c081870a6040c384b020619298111290516021a1825007000e001248201241a0f002618344040a203440487800a88092b00440c001870b02160f002a182012700430e860d0c1c0034304958021874306860e001a183800686092b00430c938021864ac0110300a10b10162021208834180a028100602099278d60240a030171988121f15c609c6090281004c3e30447c571787c262718273c1c4e1050a1c69612c00a10c00a0e17042650920e0034087800e1010903418050200b8c50a280880a10c00a10c082861208810074be30527a0438405134044078485289ee304e892b00162b0987c6a204e64f2511488e3511a13f0911c609d12560421364b0d97c6a2250709a2387c1e025288cba1810c1180142180142181040e10c08206110601406020682811c6a25544e0f001013943c09e3512409c204a045022680880e0445010a1c149a2d0b8c13624c1e0871a87207832944994911c62250e9a0438405134044078485114042878486810a2280840e0a4d0e97c66247a6090440803a5f183d382697c60f481844707814b2207a7a0438405134044078486810a2280840e0c2421208834180a048140803014238c650016003400606042c08414080280c05c6090e1404a7911c6a24c0944719141296800c1400606002c00580082810050200b8c111c3c1404a238d439813c645044405024100501718243a2911c6a184a54a22515c6a20466a0030500182810c0c005800b001a0030502182800c1031187105181130780131016242c46184c30587081408030112b8c131c14050180989c6090e0a0281004c3e30447090441a0ce304e6e2b13841909f1a6e2f0832c3e304e683800d021090441a0c25718273a1107400d0883a0060048220401d2f8c149e10c00a10c0828740850883a007001046005086005c6a245086041038430208183e1a04283a04500088a02143803294a522089c6a1cf100509408a200a2280850e200a2280840e2008629488a5f1889350214220e801c0022280840e04802050101121c609cc1462b1185088871a70431588c28871827382188cb887182730481a0c02810050888718904d168943a10238c4a2012c461b0837c6650ec006800a2a0b808d8ac28805f8c121812c561b082fc6650eca8832e11c6094cc0058008168802482238c121c11450250b8c9009ce1b06d128488 else (if i < 19 then 0x22a04420c18080811082205122911022108894410830207f10440c18080811082207028c95038162241040884187e06430c86168b800f001e003c007800f001e002080280c04c4e30487040140802e3240223e2b8c138c24110683014050200c04132471acc571789c261f18273a7b8c138848c00590c465f1a86131990c56171827439a9145a204f8cc31a8b42a271826c39a3d0a84f1a90c39a08842c561b0836230c26230e280240d0602810050200a21c62b800f001e003c00513092a12270028483c0078009178017021090341890e304e6c04209a184130904408030a12717c62412080180989c6090e090401004c3e30447e00385870408481a080262f8c509c10030112809c6098e0a0400c0404e3048705020080261f18223f021c2821208e2f8c13950682a006834150030284c0848742604283253022254380868609401c003800492080490683c009860f001c20206101030808200a030112b8c131c14080280987c6088e1308834180a0180891c5c271ab1084c220d0671825384f8bc2e304a5c203c3e1178284ac271a7250384078008441a5e2571827320e80142980141180100c082051e8571b08c3950740080e1e1297c62404a6088281003c252f8d3e10141d002c2028aa02103002813e2f0f85842471a80d83787c2c21238d385023c5e161091c69c3c14e2f0c99842471a8c2024a07080a0a8014218016101e003840505400b080a2280150981040e15426041042521180192a1c0434304a00e001c003800492080490683c009860d161a10345a10545048642c007450402530b004910061c2456044c1e00509600503600583040c182022680830f0608803dc6a260e5c182022680830f060e0c1090341910e30466a0030a6004c081854007060a2a80830e800e0c145501061e0c1e0038305054009800e0c1415002c182c081850a6040c384b02061e0c1415002c1834007060a2a80830d134041860d0661307c609cdc007060d00109834180a040140510e352c0041005010478c286519830571a5c1834007060b00160038306800e0c1a003830614c00a06c00981030a14c081870a6040c384b00281b0022992025c6c1cb096040c34f0678d839212c0818705600503600453a5a2b8d832a0d056040c3c512297c6c1952682b02061c6433834571896549e14c00a08c0098104083c1929c478d84084f0a60410385302081d259004e300c3c531c411e29c2991c64204280e94e15496432f8c84a02583a5f18951908ce4a41c5100426100a0028b0d081a2d082a28242c045450494c2c0124401210d10102880d101a203808688092b00440e880d101216002a20248c005440494c2c0110401210b158413141e00382040c10206081c10206081c1020a040140604e30487050200a0461f1822384c2411050100648c5f1a98530 else 0x1024104815040c11082009101024110f09104812102380112608848e8a0d1412682020a116088410220a4380131416202c204220a01c60901f0023201022100898104c15030d21080d89113006c20c1008441410013050483042608088649018409c1c4130882a06224492160e109828206a0e241820304234206860d02d0a3248222088340a1a101b10641098291018450710280ac24a48128506084822100e10904421084421083420904406192411102511104822040c220388220488890836124c288848a0888220d02060d0ec41d0684450407088894498422040813610c2902108889b0844064d01c203252220a4510384d82c61c82c44d82c40384444a4441089206609106494c24a48948418110806084418107c18107c18104110106498840c220c01864904044c04220c0106032644842f44422f440c8498848892084418030c100844241030071060221132106060210978851c3085113110113208440c2d022f465e0b40a32640a20502307182207131307112a06124216230b06192a06105185830e06148b06092a06160e181c25d8185232f3158983918b032506832f045e84bd080c23102a88130e88900811838b06084414440c89084011448c328362461625511045e141208c1c60881c4c4c185830492c48187034184ca81c58304284981870341b0828260c124c0e281a0e22ec0c291b170711258b030e06838a07080c221024071113061212201442122420362444c01a0a3624402028342425142a28314a28408048914088b0341861422c0d06201024160c1a20383068808230710201410244c1844481a0e3c5821890c10278506470617051e8f16083013418c128542506404c1488c19025850606120661405262d18102510104818048c1185218093d2a14088c8d0b440b0a9e89110e16182c32208e14181e14861e0c220c881985014610062150824330a438c200c4286110661404262c1010302510330a028d0a19060608c2832306214321886198521c888c290e1924330b04220888c2c508444083064202c2c118218101985820688c2c0c870c1411824646c461e0834602304c0909502413044c103028f451e6260a34640a2812322c280819187811850f0b82083d852207850103030a024051e148843c1080c04a1508203012858f0a44881809428608070a842247854190d05212604820c2804090785c10485a20585c10485a20408c2e08342d102040385418585226083c280818185006110d3d85226084462150943130b82091885a18785c10485a1848c046143466158818211812330ac40f0ac44f6084c290e048290260889110c2b1110204210203e1048101048101510145020871a2a08448c220808404308110a2a06430c22080811082207122911032188894410c32208310440c180808180808040820871)) else (if i < 21 then 0x88a2d1181207a10983220f223801c7a10f2102a107a209808241c61101e8c30428f46420f44130600c052159101e8e151e88ac840f46428f44080400012c10d86096085c30443c0a2041b0684200904630803420804820c8202090202318642510651a110c251025821f0c3f0c08200c08320c0a0818a0b1016182c204260a0824080246110480e30600820542130551286241004c14131016182c20400982820502220550c2618340a131187450c002840d8813452686c461d14326d1428291420283424220f814511110522b0c40bc2120204c3a2040510162822109044304010848242820982440904512344411861c1180448d87440a880b2a091411101510126c1088c2111104891104081004880812082408218683e05103444118644910b44081040083a0d081a830e8610842203098943080a182c506860b101100442220200802211350a1210891001c06840d42072342421908840001909044308c2110cc49442c4218190e30ea52064390410422461401440ca28083a2b118742128b420a8ac40a8b42083e0c088a442186007c18121089102005100818103010430d0883a106888110834240884186018111410030120819083106188c1808084242080842e0070422441606044504860858221032142058191830948481c88484410c2106c5a1c40c8190e305026205510261910861020109c28222028422441322b28309911941884278009481b06841f09e001920482e0c8c3012c00324098481180064a1809848940c942442c043242260019183414104c14104c1b1401306d0c30682a86184e10dd001a186c1a16141068268218260a844150650dc2028430f8018481a10481a10841a12201090340a1a2010903420d834861811040d8e8809101440288a2041b65410382111861c11800d0c3b04608611068411068420068443041a8809084488220d08360d08200d42208421828404220d081a1208360d09041946861b06840d0c848d44049b21849b4690c3821122028362040385048808141a111087850d1a440980084814100130504130945004c25430c240aa18613842e09a04617060584042409a08609a0c41305040d61c40960034304b062095081a18340b428c240d081b0d14102302131a2893084408178430f81205c9b0861490882048a444148a205e0ac38e0ac026c61d82b04309044209044210044221c22006841744441742841108041708841108044384200d090a08481a10701a10701a122010903020903020f83020ba20209030200240c082e0c21860c8684090a14402120604120650830b83020b03020b83020605828622022102430486082811848d878488118460464a82050461c44a8221182205185840c9504082904610617820503c2024a820504060908520813170811298b040e080c1214612a0818 else (if i < 22 then 0x84e30404e284822262c2c48612c30820c38a120c24184b0c204820000dc5b103c5820d04d06362020d618405841a0a080a0d88154309860961d0b80204813410c240d080090368a192584104816282c3058ac20824084814048c1a05080612088a022606080204a309c2130541281203408c50c08c38898046106178412084814102813848c13048986c2c2078405878409878488138488081288154309860d6021232521220684a2250102a58282090340b42128584089542880812080a0d088642c20683a2844582210304e11841a11811129081210941211811129081022094087c813c2086309c11874087ca1e82501801487a12782212800f901ac508221061c61127426094095844c081904a043e406828209c210aca1026128a00983686183414888250f80304f091076800d0c3a0d881a09a0860941506361d0b0818760942608849c1841106840904220d028649610449c1b08309044202421109054484220d08221208400d24412441c3042230a3001409c1c6c2c1858307060b130710270710441b120e84104420120c1088342080348418343a120c10691184183414104c14850c260508878304260d818783060b0341861c81c412068412068421068483050608481a1001206840d0e040d0220a322020d4184004414106581104c14490c23084c08110c1480c1c6130882606224494114f06104c14450c1a8388220d02474b26841102d0826202a840d8d32083408110d0608441a1108324d0c1b0a2892c22688538240d06241206c20c9b0341860460426345126068390328a81b089a2a3892046060e54540d061d109b030cc7040c94e329c1185188209103013410c240c080808302414113c104418110c10883004184418107c18143086106618430e184409140827048c8d87820b040b1187820d1809c10602064412060402060404090443c10483a20444c104110604110604003022103210606428620a28190c21011226202c386041306012341200151a0a18547a20602682182683108604c10c308a8230e05c0189e04c1301192844181460861e8e3c1841461106041806041006050c4510c34103044230438202130104430520d018290240cc1061208840904240c02061609040c02449e84411e81470c81a0c309c2c585880b0e161420909c40a6204e30882807182611408c26c48893084c13418c1a88a2509802d15804d0e0a4560c61484260d02c7084451780222181122181122992c18d109489114460462182304326a2208184c240a8208400a51234420009184c12120ca4880a890a2289c08e890a149b105289104c0a120c9a888822108b0843889a8588275089090852109836226a2228a42848426110441042207a87184c06120c230489110c650a948c861949c61921c41d0c90d29224e88124e08442188524504 else 0xc585890b0c1614213841a0588240a02460a61)))))
def layer511r10 : Packing := (2119,3,6,63,0,16,1,packed511r10)
def keys511k11 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x18e7d9c6ec3dd4296c4809c48c608db90d561d18c9b8245ac41c0000000009dad5cded5e6db6c00011610000002fa1e84d55bc2b4989ee0e1dbf7983cc9880000000000000000000000019664000192d0a06fc8cc00000002199e8b3dc7f3de3bccd994c383bb19bed5cbdd878b8450ad586318054d9f1b5fc9c9ceeed035c653817315514ed95deb17b9083e45e0941ac0bc00011e530c2e95f51e345e4a44ec0001d79384d655340f66154cc828609954b91954d0ed4745d951c2d7d7d6c7c6d35901c50253820f9754961b011c0a8344a3832100875bc4d3ec0000000113ac1b180e240005000004e030700008070780008060581002000807c203c02810142e030740c0100004060103008000000048001f1d074040500000000200034001c01838440b02020022b058101e000000802410180030040100c0a370100438060880c0205060100029090100e2400800000b03000000000038140a00078001f008480c0000804060801064020100008080d018101a211e8001a00020bc02680a82c000c218000c020083832010a81406160100802070080414020009c0a030101404000283022030109c40060200c0603000841c090680c0801020e022011085c00020101c000907810022704820240e0180016071c018160300820040c0283002000682c320a000440400120041213008000a0d04800940200810020001814141400020100d00024080a00008020400098000007000720f0281c92106181c220a0005c04000008c001901010060c008141c000006c003d030040008018242604118401a2501004000d048000a3f038ac1208030000a050580c0c0013800002b04034020a0a0601007008002601000040800070040003008a4420d06028180f0102406050180000421401c0000110142005018940825048b0020529808100b05014000300830200801800000c030000400038000603000002000000040a0801050200b018002e000003c0005008000006070001a0b030683a710001c041e0000800000001c020205824020300814120a0001806020000000000c00402000102c0892028b00000040641e01000140003018b41c02060203c0a038040a0c008080a000000c000a010704a02008b07037000000e1a0482410190006020030004016280f83074050089406000002c02020003402001481c26480884c083803000100111810020900810002a0700404170200058070f80c0030000681605018003015001cc00070381848010485400020882c0800018300312008041a060181800000980000130087404090381424000688808031a870040000050661e008040409020000e0d0505c4227020080415028000c1a038300202060000611010581a05100280839150140e000180806010100c0201108581806008500811000081205 else (if i < 2 then 0x81fb8b6f8ff8d2c990d0c12c60c01a8a0cb0dc915976606a8cfc0fc1ddfd4c0d1e7b427a20941941844a9e6fcbbb1cd000cbd05986fbde65d4c6c892c063d91ed5acc3b58fd00000d6af886e97a3596c0001465800031d425e580000000000019fd9d779caa6c9acd1dc0fab1c39d0bc5994972fdb99415a942b1f15102ecb9b4d195256c12411ca5a8d0bdf522ccdbe10dbde4000010b8cdcf19504000041b8917f5aca928fd4dc9a9a82ec92900000000295880002c6f1123e0ec1556e1ec14c8000000003da50cb78859b9c7c00010c078c69574c0000000000004d1319ebe09e4118927c4f5b0aad5a14000000004346547b050c0003133c000140835d9f8d1614fc0000de719413d67000014e980003978b48d306e6c80509b045a18c7991e9c66c4d979d10207f4eca8aec0001c37e80f75ce50d40000014b40000cf2800021ba0018d5251cc89cefc00021a540002428159f102dc00000001cc21dab580da898793d903f4000000018cf3cc519e95c0c094cc0000ddf04d4400000000d0e00003c8b8000150380000548d9e8992bdc82e1b55107f46cc0c34d12255be4e708d98409c44d800021a7e89bd870800038500000386b391fd85dbd0b9d40fc04055b30908000194d4000257bfd2dc00029e15c61f4abb8c751f368868c9a21966ce2220ee08e09f5a4cf94f3f49cc94aed4a858a680d61a81d6f49d72534a980ac1ab13265698d9280003081ed73acd844b9d43b199edd7cfc166d1a4ddb6de12a05f8a3bc0b81230453c00008c914daa495f5aaf8e344e8c9c400003504b1c0fdf289d2199e70ccb8dc4d47d87899443de29deafc0ce8a94113796efc2430968817554e61aefe02b45e795d8dfb40e1f132ea0cb9a441c8e9abfc8570e18000000000af0000000038fdf0e6c9e804654c84491a8529d88840002109157618b04c3d39894000356b658a2dece9985ca730d4c000093280000000319c40bd30144000303fd8e2c5146597eccb79a8647dec115d674c93ec990db8c00038bcc825406845cf8d10a4a35029149195afb8f72d92400005efa49abd10612581708a0dac710000259f404cc4fc91d5c13981c2ad4d9dd57c1998eb49ddb9e32dd259a3b5d00000000028accd71b0a781d7789ef98df8135e00983f0556405cf11e1803e51315283dd914e91d0e91f551606430f9bffdda5099783c5c9538797862613a7dda1daebd36800000003cea7038f53e513d711d00002455a1c590b3280ec0003d514000260ebc13f153a50650fa09fd7df4000001d331d44cbf01795913b4a21833c00029e57185c093a8d065a9c907a1509138bcad381b4cb880003437a12600000e0a94c140001942300d245215eead7139ca20b5d05b9d90091035765c2728099dadb587ec610139686af4f53909518d3df88000340f98c9b90840000 else 0x16c450aa05369c671e0360568bb699219cc28f0e81a1dc1f4f40ddd1cd711b760cdcc64919a70f4d07b3d5844e5f5ad65ccd20f6ca0b5e759f0d14efc1f0d4731f8ec2e30780d8668bfd1da9df6b5ba8c18388db01df43a0007e20d45b100b940001dc3fd2c55bd0457f569c00010df9caa2143a18345e98cc66da61d859d5d1c32ecaf694e2cee45172515111c35ab1df7906359a2782c19c770ad91cbd94f80003c054a0900003563488340003d69400000001df2d4b71c4780003c7d74c7000000002c5538fe88a5c00019ae2d784c9f49195497c00000000000310454a75131c974985f5473ed8bf8c54158c00018a4856500003129781e09e1b42b948730c2a467b5800000306b8000199140000cd57caea049e8112e02357b0c476d6440001e110930300b40000d360000248ebd64e003b07c39f3000021cb5566cd070cf08000000004445014a96ca09a40000c08b9aa5079000005bc0cd5f0b4a1c7390e48799d5a843a400020372a0f087fcc3cf97ae957401fe81900abd0ae400000003c7171aa206a8000257dc03ad5fba85480002c84dcb6000000000003108f50ddc0000520ed30958f912d400038e140000dbca128749e4a01c436ec5edd7ee854d17c2460e40e9d1c68df6129a1c254fb25d7d8d800e75442c000000024d084d29ce6247eec9ba4bbc0f10000349024e86e0788e0a450b08d6c76302e718e40002c47cd65d4bd485b69ddd810f4c9747e79405c28b1d798b218d63560dd01450ff019c1f9642015ac61474ce32a02f5a6c0003506fca4ed2000000000397418ae0987890df2027c00e55f800029988000000030d3b0097c2f1d14e4cf7d93483c00001959556a8000000009f5e9931889c0001cd5800010c59ded4000056d6896550c7ce0d02a29ffc0002537d171ec7424bb08ff6d3f80002412bd4bd1bd4000000000002505c5d49936657c7d077570f52eca08c47bc8a300001913e1feac90c4be58ed59f05c8e708c25341c3280001ca6c00034f25ca0e18ac000318b5864c00008e39c4a9d6568d7e0f46c18604a653d31a42d8ed46de900c90cd1acf8b835d684c8f1f50000110c8000000000002d5edc3888a58000094589fc8c70546741bea823e80ddc0c70f4a899f8874d909dfd38c028331935709c00002557dd86dd3f247ae96d9c848d97bdfe5d8ca8ac45bac93b81c04df4845630cc7cafc42c8075e5b5aa0d2dad28e04088ecba4dc529d8f851cd6311891d2b5a0a408018e898a42c28584869448c15e1a6acfc60c6e49494a600f2358ab4ab458271db0c35000000003604400019be021144c7c0000025f0b258b5a92a35d665fc549c65a9400021f1a0ce296d21d3e1d2fc16fdfdd934f15e2c83316f914654e130cc350c249609bdc1ff655b4d5bb545c063e4a53a105562758d88894a04b0fbe9a07)) else (if i < 4 then 0x8ab0d48a58bb4f90e0e61faa06044d679f6d9bd9413ac0721fbe031c55dc824c00009822435d18e98e5856fec7a400011c620315de0951d6d305887f5cb84c4c000353169335c7240003521400019e0c4e2b451b1eff9b0e53c9c681410b981d5648a0bd112c5161492d874b045c4bd85b870eba43ec5c198456cdec1ed345dd4359426884bbc405426ddbbb4773543e9372e0af9274c6ff80088576dd94982c000393230be9c27eda7782f6c2ce155ece4a90f31c1090f7c8b2921a55258dd1c42501012050005256b3528b0c48455de03c59b4d38e8a3ed79d10991874919ace475ec65de6c222c32684fac0284f940002d6a4dc161773148007b6873803d604599c5c483a17e1d62fd9c8c699d84393834fe603820d8cc81b074fc3964672549b031b04aca03117ff1b6a5776576892060bf597a400000003c7a800039735124b4f89578e500b8cb85e8ede2ee058000043a90432cc1995fd1377453216b80003551c4ca7915a48a1c6c7175e9a4c12a5cb2bc7280000df1dc194000059a1d9e288b4c7bbc04b4b3a4ca3cdf219d11b51995d8841095554c85a1b5afc839c939f18e0000340b000024e011579511800025e275f3fc7540002d4855ea0d0b2d3ffcf1f178220068dca919e573220c6dde0c41e8bc0c27684e210f918b3848f863b17535918df75059281e548de5ebb0c400001152eddfacb1cc583d88013eb16e0c2a74fd75b020dc0906a8a2400008a67568f14460e5511ec0003610fcb915c4781a494921873c4180b1282c6c61a0eeb5608885212b30adf1848875b40a8428e9a1dc8610422c5868a2c0de0580f44eb41f44e51c105d68808a44a1397d30338d9fc14d3d72897b6cfb9d0330fee1ec95dce99ab058bc905cb5706ec4225ccaa47e80003843dc2654aab4091a10015c31f9118f7888b57145ff357040a298f9eda7397e400000000000000021238cf8c000344ff9f830731cc08d018000390291512805be0bb19700000e10a81239b3400000001d3b000031f01de4c10525cf51fa0cb7fc2ea8439c784000180e79d0b8fb408ed18288f38da098384cd7653df0151dcff59592000dbe48c45871d49ffe0ce86d79154cd6fd40390a342b04b6ac0a40dceca691ee405388b0ec01e59d5823a9d07006cdb040003dbef51b760a31cae1b491c8781685e07d187db3287d8000317f84fdb14f400035c811542c57b96841bccd1118ccf5cd71a6584c5cede40f05d184e6bd1ce9d1589838ac18377cb365ff8d1bf9ebe142d07cd8566c720c304586bcc62cdfe42af19b0984e9f094b64515d88fd9904000182fcc615c473803400000001ce6746a400029cb3d384d962d2e18d78cf60000258158b470ba18826ddc49ccb06cad2fa1b70cfe15ef000039defcfaf4b16567be018000390b6c3669a204cbf924510551aa99ede else (if i < 5 then 0x812c34841b1d1ac866bceae4b18cf34c820d3455b7c12650ed34bca5db8d3301df4153cc81655295692c04f16bf4630917b420b16000a1941545992cbc4cde551b30229007a4caf49329c0ad7d9d6620f75885d0be048c64e790400c24400031f63c16000011ee04cee870e5ef7e00d9f2784168dd8da798e4fc3da998e126d5639901f43c89e9d9dd7c8c9dd6e1b63d18300e30ba81d5a04b4946090d5d3105b95dd1c8f84862206d298c38945c4298262d96bd4b08a1dd14385cbce94000000031bf812cc00004ef8021e454506bc0002d41d9547523491a008f34a45111cd1db4399ceb392afdeaa536ce03acf5f49d0d7f04cd7598350104b74871b04f457ebd22106639a2c822c979b554b1e3d9e694dac0003869305c785bfd21f00200af8d007dca800021d381b2000000000000000030cd14217080b92d8546d45fe916c193d1177cf6bd76e60f84c8791144f2e5227567f092a9d4c000356e9829d961407755520d43701ae872fd5cd0978c5f0079fc89bc85a530c15a355314234817e8019e0b752f5925c000152135c4cc7cadce1963ddb24959bd2439393096ccd480000cd5015909bb19f66480ede5c91f918ce2072d90d1d9b01cf92699ae4972412c00003846d05f80deac004825b52aad8f04c3f606643e4d10e008c922a5f3a4a8c00000002158306a09c2c4557806849e1db3800018ebc9f9b98305f7dc2105e7c47004fcf11919a350ee2df9e459400020667c437c62c00000da40001da03c7500001c7fb8f7800000003da3fda0e01d39720000143e0d04d16e4109d4e3e124f89f2551ac1ef1dbf4e43dc7a4f0404120ff31dc0c2bc8d2c10a51a499eefcea80000cdba062a5f11d18800018d6ad703deb5dbb68d0fcbf85912cf998142851604f0468b407657f4846216f35408487ac91f8b51e012c30206c3566ac7781c9c00015c894a0191e6c1d882194c1dc4c89cea9425dfef8bee86b400035682d3c782a8116b85d1c9fa846594e905c35ea60a044493dcdad4a08c5f434c12e841ca04b2944c0000e04fc357e087d6c25c31c9421148000391299d811496994a8f18c488000000000001983a58540768000051f74d3f549d0a17c29b08fa0b0b877c42079415cb4f0f0094531ade159e494c903c8a7e58c488aadab91643ddcbdc988452c4c2181a440edc68000291bbd61c49240001993997a95c00d456c52d4da0000300a2135e188b00151c34562b15a61c2284e7d94d17449b7b13bfc6f6df8492e413e245e844688fa404418ef75a93d62150405164c78f1d510cea81ebd33800039a32dcc6cb43095ac8afcce592094ef20d245fafc6e047d2ca878d8b864404be0db589dc5c9759d96016d77edba693c20643d9ac53b605ab60ffd02155d6c003c02f96cc5af3988583695b0b869ccdd49d619569d9c253a00d37 else 0xc14d467f5b9fc0655571cb2edf221bf1dfcc42d28334000204940f5520600000c59c0000000143419fb2465ed8471a1285a4c40856dc00030a9fcf6c04dd5272818b4914424a5b2a80464d1f068c0ea2d81203e959fac99a098fc9d60362d94482324e82db4615038f17d73f199ac9eb84994867cc32d2f01ca620b385704c9de11a476498995eb258d580ff5278000392b893ab05125b1d94f30695c01306ea60741d2b97c80002e043805c00000002d08a5b3c0000000086d8000190800ac800005e440003902419dd8f338c38460220809b2e05d4d3509b4014a40002c76c0000d9ce09d945b309b6030ad3f51d0dd8fc0000d851988e08be07364ad50d01d75a4e9d844d137b8972df70c3bc0000000187f6802788819f4e4f821a2bdc54000347e00003cc10000291f003f881bc00000002de2000000130cb0084d39cee5e9095c74d220504de1c5ac01d8ad1270a8b83905fc2d46ac312c911052a19bbca579a5e1af787a14d9000029b14000014329d369557931b150d40adde638569cd3000008921c975058c5bbf02d80002a0354c27ca90dfa60f7c0003c17816a3506095e8000015f020df8a989edac5400db19f4420898ec40936c525108e5b6412fe565a01d6992cd3cc00001fe3456d5a5bdb8b4ecd4ffe0bac5b4f5000)))
def packed511r11 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x77efe484efbfe889dfbfb0f3bdffa6586dff4430ddfe7761affd32bb5ff66176dff442eddfe775dbdfb0cbb7bfa2266f7ec3ccdefc8799bdfcef335ffa6584dff44309dfe77613dfcccc25ffa6574bfecc2e9bfe885d3bfb0eba77f9dd74f7f332e97fe99592ffb30b26ffa2164bfecbac9dfe77593dfb0cb27efa2244fdec3c89fbc87913f7cef227ef61a44fdebb4897fe9960f7fd10c1eff61d83eff3bb07efe6660ff7c88c1dff66173dff442e7dfd875cfdfcccb9fef91173bff4cac77fd9858f7fd10b1dff65d63eff3bac7efd8658fdfaecb1fef91163bff4ca877fd9850f7fd10a1dff65d43eff3ba877fd9650fdfccca1fef61143fdeba287fbd6450ffbb06a1ff7a2233feec3c67fdd868cffbaed19ff761233feeba467fdd648ceffd32c16ffa2182eff3bb05fbe4460bfbc66c15ffa6572bfecc2e5bfe885cbbfb0eb977f9dd72fdf222e5fde335caffd32a15ff66142dff442857fd9750bbfceea17ef61142fdeba285fde3350bfdb04a15ffa6532bfecc265bfe884caffb2e9977f9dd32bfeca265fbe444cbfbb06997fb60932ff6b9265fee8888bfdb0f117fb21e22ff73bc45fed8488bfdae9117fb60e22ff6b9c45fed4388affd32c06ffa2180dfec3b01dfe776037fb0cc07bf99980fde4a301bfd84603f7c88c07f78cd80ff7113017fd97203bfcee405ff65880f7f331017fd94203f7c88405ff64c80fef199017fd92203fdc44405ffa6570bfecc2e1bfe885c3bfceeb877f5d970f7f332e1dfd745c3f7c88b87f78cd70ff7112e17fd981c37fd10385ff65870f7f330e17fd941c3f7c88385ff64870ff7110e17fe99582ffb30b06ffa2160bfecbac1dfe77583dfaecb07bf59160fdf222c1fde33582ffd32a05ff66140dff442817fd97503bfceea05ff65940f7f33281fbd74503f7ac8a07f78cd40ff711281ff980502ffd32985ff66130dff442617fd974c3bfcee985ff65930f7f332617fd944c3f7c88987f75cd30feeb1a61fdd434c3fba64987fb88930ffcc0261ff9704c2ffd32905ff66120dff442417fd97483bfcee905ff65120fdf222417fd93483fbc66907fb5c920ff6a1241fed32483ff300907fe26200ffd44401ff897803ff30f007fe21e00ffd3bc01ff986803ff2ed007fe61200ffcba401ff964803ff307007fe5ce00ffcb1c01ff943803ff305007fe5ca00ffca1401ff9328037fd110077f9de00f7f33401fbe44803fbc67007fb88a00ffcc0401ff970803ff2c1007fe50200ffc98401ff9208033fb0e43dbf65887cff444efafe8899b9fcef336efa2244edf3bc89ebe669137bd1119f779de33f6f33467f9e448cf7dd111177b9de22fd722445fce3388b7f300404ff66070b7ecb0e17bd941c2fbb26385fb64870bfac88e1df9701c37f5110077e9de00f7d33401fba44803fb467007fa88a00 else 0x501fe41f781efc1e801e141d981d2c1ca01c241b981b2c1ae01a541a08197c193018a4183817cc175016d4165815dc159015141478140c13a0132412a8121c1180110410780fec0f700ed40e380dbc0d200c840c080bac0b300ab40a5809ec0990092408d8086c082007c40768070c06a0065405f8057c05100494042803bc034002c4026801fc0180012400c8005c0001ffe9961fffb2cc3fff65187ffec9b0fffd9261fffb20c3fff24187fff444efffc9761bffb0ec37ff9dd86ffe4c2edffe885dbffb0ebb7ff65d84ffec3b09ffe77613ffb2cc27ff61984ffebb309ffd93613ffb24c27ff64184fff4cae9ffd985d3ff930ba7ffa2174ffec3ae9ffd965d3ffb0cba7ff5d974ffec9ae9ffd925d3ffb20ba7ff24174fff442c9ffd87593ff90eb27ff9dd64ffecbb07ffd8760fffb2cc1fff61983ffebb307ffd9460fffb08c1fff5d183ffeb2307ffd9260fffb20c1fffa2173ffec32e7ffd845cfffac8b9fffa2163ffec3ac7ffd8458fffae8b1fff66143fff44287ffd9750fffb0ea1fff65943ffec3287ffd7650fffb24a1fff64143ffec3b05ffe7760bffb08c17ff5d182ffec1b05ffd7360bffa86c17ff61d72ffec22e5ffd745cbffb06b97ff50d72ffe482e5ffd8750bffceea17ff60d42ffeb9a85ffd874cbffb08997ff5d132fff4cb01ffd97603ff92ec07ff61d80fff3bb01ffd96603ffb0cc07ff5d980ffeca301ffd84603ffae8c07ff59180ffec9b01ffd83603ffae6c07ff58d80ffea1b01ffd92603ffb04c07ff5c980ffea1301ffd32603ffcee407ff5d080ffeb9901ffd43203ffd32b87ff66170ffe4c2e1ffe885c3ffb0eb87ff65970ffec32e1ffd765c3ffb28b87ff61170ffeba2e1ffd645c3ffb26b87ff60d70ffeb1ae1ffd435c3ffb24b87ff60970ffeb92e1ffd425c3ffa64b87ff60170fff440e1ffd841c3ffb04387ff50870fff442c1ffd87583ff90eb07ff9dd60ffec22c1ffd74583ffb06b07ff5cd60ffea1ac1ffd80583ffae0b07ff66140fff44281ffd97503ffb0ea07ff21d40fff3ba81ffd96503ffb0ca07ff5d940ffec9a81ffd83503ffae6a07ff58d40ffec9281ffd82503ffae4a07ff4c940ffec0281ffd70503ffac0a07ffa6530ffecc261ffc984c3ffd10987ff65d30ffec3a61ffd964c3ffb0c987ff5d930ffeca261ffd844c3ffae8987ff59130ffec9261ffd824c3ffae4987ff50930ffec0261ffd704c3ffac0987ff50130ffe4ba41ffd87483ffcee907ff61120ffeba241ffd83483ffae6907ff50d20ffec0241ffd70483ffa80907ff4c120fff44401ffd87803ff90f007ff9de00ffec2401ffd74803ffb07007ff5ce00ffea1c01ffd82803ffae5007ff50a00ffe99401bfc97a237f921445ffa6587dff4430ffdc9361effb2c43dff65087bfec910f7fd9021fbf9313bf7fa22) else (if i < 3 then 0x28f62610a0508634f8388958713978d3a56261c5e34b82938987178d361a54265e34b83869309978d361c225e34907889521978d36265886349078920978d2c1a24865e34a958987178d2e0a4e261c5e34d8689178d221e22845e34b883c298611978d38a62658408634c37881b8410218d38b8a658408634c29899610218d3628a620f0408634e2989961013801d38a6265e3084b88958711978d360e224e1c465e34f118986978d2e1c42265e34a878910a1978d3446261a5e34b0f990f0d0e810e050d790cdd0c310b450ae90a3d09a10935088907fd0761067505b9051d047103b50319027d01f1017500d9005cff80fee4fe58fd8cfd00fc74fbe8fb5cfad0fa24f958f8dcf830f7a4f6e8f64cf5a0f4f4f458f37cf2a0f1d4f138f09cf000ef74eed8ee4ceda0ece4ec18eb5ceac0e9d4e938e85ce7c0e6c4e5f8e55ce4c0e404e368e2ace1e0e124e098dfbcdf30de94de08dd6cdcb0dc44db88dadcda40d9b4d918d87cd7b0d724d688d5ecd520d464d3d8d31cd270d1f4d138d05ccfb0cf24ce38cd9cccf0cc04cb78cabcca20c974c8b8c82cc780c704c648c5acc510c464c388c2acc240c194c108c08cbfb0bf14be68bdecbd20bc84bbb8bb4cba90ba04b948b89cb7a0b714b678b5fcb580b4d4b418b3acb310b254b198b0dcb060af94aee8ae3cadb0acd4ac48ab5caac0aa04a978a8cca830a7a4a6a8a60ca570a4e4a418a35ca290a1f4a168a0eca0609fc49f289e4c9dd09d049c789bcc9b409ab499c898fc984097b496e8962c9550948493e8933c92a0924491a8910c90708fa48f088e8c8dc08d148c688bec8b608a8489a8891c883087548678859c85008424837882cc82208164811880cc80307f947f287ebc7e507dd47d487d0c7c707c347ba87b2c7ab07a3479b8795c78e078747808777c77007684763875bc754074a4741873ac7310726471d8715c70e0707470186f8c6f106e946e086d8c6d006c746c286b9c6b306ac46a4869ac694068d4686867ec675067046698664c660065946518649c643063c4633862dc626061e4613860ac60105f945f185e9c5df05d745cc85c2c5ba05b345ac85a5c59e0596458e8587c58005784571856ac565055d4556854fc5490542453b8535c52e0526451f8516c50e050444fc84f5c4ef04e744df84d8c4d204c944c184b8c4b104ab44a3849bc497048f44888481c47b0476446e8463c45a04504446843ec437042f4425841cc414040c440383fdc3f503f043e883e3c3db03d643cd83c8c3c003b543ac83a4c39e0396438e8385c37f0377436e8368c361035c43558350c34a0345433e8334c32e0327431f8317c311030a430382fbc2f102e942df82d6c2cf02c842be82b5c2ae02a7429e8293c28902804276826fc26802614256824ec247023e42338228c22202194214820dc2 else 0x8c3d405486205c1e30f4f88178c203d2a4a42221c5e3254e9492908887178d3a545e3284894908883178ca13a4a421a245e34c94908716898d324a42221c5e34c87178ca122524a42221c5e34e1a18138987151027978d544c2c1c10f04420563522813101188a027978d4c504c442c1c160c2635211882786978c293c544c441c225e34f1511862796898d38a0410c46189e5a263531513110b0704898d44544c442c14221e3511513110708978d3e20a0528658f0463501383158d11284e261850406e325d114978d112618f0a6585630bce09158d11228620f04658a63105007158d11204e2618405066325d114978d112068605624465c863501a18080711882721978d544c442c241c10f6351150b0904118c213846261a5e30a4d1513110906978d38a044461e5a2634f1513110b0704898d44542c24108634d1513110906978d3860a6209e5840863503c15118d21285620406886325cf10978d212060a6588630bcd10098d21262042588630f4d10978d212620de1c5e30a4c941208278987178c2948544c241c5e34c1588a1178c2934504c241e0e345ce121188a0178c293846185a2630a4d151306898d1734544c221c5e34c14130987978c2f386862504c46189c265e355130b07043d098d38686054409284265e35314130b070583098d40504e1c225e30a4f15130708978d30a450404a809658be35314102e2586978c2944544c2c121c2634f15130708978d30f050ba561e5c26350221a181511218997078d506860244486209c1e5e3543d130b090495078d40686054408e265886353150b09058c213056241c825e30a4f15130906978d306860541c408c82265e35515130b0489078d38a446208e5e3084e9410202388978c2940a25040cc40808e5a263542c941110238820bd8c9754544c241a5e34c3c1520958997078d46265e30849118987178c3d30482446261c5e30f51130907178c3d344622845e30f4d14130907838d17384c461a245e30f4f151306898d1734421e22845e30f4f151308878d17304c462042805e30f5011871016898c3d3a804624405a1e30f50158987178c3d3040a63254893108a8886858c954040a63284894928a888428878d40a2563284895108a8884838ca1424a221a5e30a4c948886978c29324a2a1a10a22634e948a868428898d3a524a1a225e30a4e928a888428878d3a18a63284894928886978c2938a2524a2a2214421e35292108886978d325042221a5e34c94928887118c973a524842221e325ce95130b0907058d1144524c2c241c160e3445315130906978d113c544c2c1c12263445115130b0904878d1144544c241a5e3444e928a8684281488118d4a522a221a10a0484635294928886978c293a5248422a1a10a22635294928a88842810878d4a524a221846325ce3d89978c21)) else (if i < 6 then (if i < 5 then 0x4e221e345d112930a8b0889068704858c951168a04c2a2c22241c1210521e3445a150b0904298d10a14452542a2c22241a1c12120e34424dc2912930a8a8906870484438d1168a452542a2c1a1c12104a263445a2912930a8b0888870484418d1168a4542c221c163442853149512930a8b04852886338d116c4a4c22241a18fa5e3445514941308890686978d115452544a4c1a18c25e34455149512930888862c978d115850f632848143d8c912068604624509e5c86353110b09043c1306158d4c56209e588634d881496218c293068f65886310cc11881418218c97386a46205658f086350218c951c4a422a221a160e32552218c911a54442c24140e34850908a8884158c213c509e261c5e30a4f13110906158d17384c44241e0e345cf8921178c2928189e24845e30a4e151109078d173454442086345cc9413881520178c29424a42221c5e3254e9492908887178d3a545e3284894908883178ca1384844261e5e310ce1513110b07043d098d484c442c1c160c2635113110708978d306860504094865c263521a18941006272109978d50f4442c1c1254263503c14958797098d3c54442c14263084f15110708978d3618ec5e30a4a9412278709178c29444c44241a56345ce141108a1178c293c504c441e0c26345d015869417098c293a4a422a1a1426325509492908a8487098d4022563284894908a8483098ca1424a421c26325cc94908708978d30441c86265e3104e1513110b09043d078d4906209e5e3084d110b09058c21344c44241a5e34d13110b0489078d3868625046209e5886353063d8d2120f256265e3084d06978d2120241e34849218839178c2934189e24845e30a4e15131109078d17385624588630a4d151108218d1734805622505c1e30a5188178c20292c544c441a245e34e14110721978c33386862504484209c1e5e35513110b043d09078d40686050408c26588635315110b05098c2138541c24825e30a4f1513110697098d38f05240cc8108965c1e35514903225978c2138e8cc52409482a41e325d43c143220402397098d4a4a422a22141e32550908a8884218d324a42241e325cc949088218c97324a422a141a2634e94908a8488218d3a524a42241e325cf898619178c3f344c44241c5e30f4e13110907838d173c4c441a26345cd131108878d173624845e30f4a10078921178c3d3c44241c5e30f4c158987178c3d3454442086345cd15110689178d34544420845e34d87163d8c312848461c245e30f4f13110709178c3d384422845e30f4d1413110783098d1740524108961c5e30f51141290313c24a18d174c544c44221e345ce158617098c3d348620b45e30f4c11890721178c3d3c4c44241c5e30f4e118916218c3d3454442086345cc1411068921178c3d44544c42241c5e34e401588222117 else 0x25e309d1129289068611083d8c9627584842241a1c225e30f52311292110686978c883d50b0544a484224221a5e30f56148a8884838d10a140a0922a1a14f22456344543c2887158ca11138f08a4a2a2214a21c563445628958b89878513118d48a256261e2a221e163523c2812118b898784958d50f048442a2c22241a1c12163255a3c290a8b08890484261410218d6a56261a58a634c26141308890686978c295452504622588630a5028958b8784898d38f04c2a2c1a1c1210a0990a2635a291494118b84898c2148ec52504c1a1a225e30a5428958b8984218d38f42a2c22241210a0990086358391495088820978c29488c52542a2c1210c8a220863583c958986978d3098484422241a1860fa5e3571495088810218c9744525048441a18c062225e35714941108882c1896218d50f42a2c241a1c121098422050a04e35e108a88843d8c952140f0a22a109a24463485226891018978d213a522064425e3484f12930889068637178c9550504c222418986a18dc5e35708941b178ca1345254222208dc5e328531293068642261a3689178d589452504c1a18d86a245e3571293088836261a8641178d5c5422186c5e3284e3223149512921a368689178d644a4c241a1852245e30a5514950889068613178c29524a2a1a142630b89103d12930a8b09068704842f8c956a522c221a1630b89502824130a8b0704843c26862f098d70f0a0942c1422563285314950a8b090484822f8ca15a524c221a1630b89502615129306862e978c295452504c1a18ba5e30a5294928b08858c2e2540f0b8944a4c2a2c1210a09a19042635e2825150a8705098ca14c52544a4a18ba5e30a52949308868b8c2e254098944a4c1a18f860bc225e35825149413068619082e978d58b09452544a48642218ba5e3583c928a868429098c2f4a522a1a10a42630bd0949286978c2e293c862e2610a41e308d09589218a8985078c2348a4862e2612f41e3255312930a8b08890484bc11078c956a562e261086308ce230a8b088904843c28278c2160a25486241a5e308d0261512930889078c96295452542220825e30a5095218a8907858c2340f08c4a4c2a2c1210a0990a241e35c242314950a8b04842888218d60ec52544a48441a225e30a563c95218906978c2340988c4a4844222060fc1a5e358229914941108881820978d588a6452544a4840c0641a26325da3d129308158a898428118d076452562e2610a0463085314951293088906298c9754544c2a2410a41e30bd389178ca03d28484422241a1c5e30f531494110888838d16a14c4a48441a190c5e30f52251914941306861018898d17644a48442221045e30f53150886198d16a1388c52544a4840c8621a26345d8151293088986103d8d175452504422241a184e345d5151289062f8d173c52544a) else (if i < 7 then 0x70485038c951376245e3280a4a151091061287898d16275054424422220e345a853898695178c29304c424422241a1c5e325551091088814218d17409a422c22121e31089121510910a8b0704843c12878d08277442442a2c241212090e328562692910886858c42244c4a4c42441a1c2632589d41310910686261b0842978d589a4a422c221631089122692908b08878c42244a4a2a1a14263108910138b8785098c253a52461e2a1e1426309538b8784bd098c953c42442a2c1a1c1212f04c263255a3d1090158b85098c2148a25244261a5e3095026241413109106861b098c9764525442442086325d094918b0887858c2540f25244261a5e3095094918b8785098c2540a62e1e107c26324511293109106863b178c9550504c424418e8986a1c245e35911081a95178ca13c525442442208ec5e32854908a8885078c4022444240f04e2e26141e30509d6282691072188978c234c4a4c424422241e32589d51091088826401a20978d509a4a422c1a163100893129310910a8b04843c898d062768f09442442a2c12109902208635a3b12931090261a410688978d609a4a422a241e310089226928b0684898c402248f2422a241a163254852269089061b8c972140f2422c1a109a26348529491061a88978d21444a4c42442220e45e32554151091088838261b178c2158e44a4c4240986a24190c5e3582514951090381a8821178d5a4a422c1a109630c88923d129310910a8b09048506338c957252422c1a109630c88d22310910a8b04843c3227098c216a524a441a109630c88d33226229b1293109032141b09078c97788a6c52544240c86c2258863589492910624978c32234a524a2c1a109630c88d3109108890612863d8d16275c4244222208fc5e328531293109106863c898d16275898904c42441a1860fa245e3591293109108883c878d1627589c442218645e32850322623129310903e188887178d68544246245e30f0850131091068643178c3d4c525442422086345d1109108884021178c3d488c52544240c862245886357898691178c3d30c0504c42441a1c245e30f5714951091088231178ca1544a4c424104245e30f531510861909178ca140b442442224588630f53129310904307178c3d48946452544240b0622458863598b898784283d8c27424e261e2a221e16309d23c28158b8984118ca14a2418f04e2c221e104630509d8110a8a8904848215098ca15a4e222618a25e309d015129211098986298c962758504842241a1c225e30a54938b8784898c273c4a48f0462e1e122630509d624130a8b068704843c2826898d68e8544a4c1a1a5e3220a5588a18a8984878c2740544a4c2a2a241210f0442632189dc3c290a870427098ca148e0544a4a24221a5e30a542312930a8b04843c32282686898d724e222618f else 0x4e2e261e10f6309d02891878886978c2742461e2a1e1226309d0918b8984218c273a4618f6221a5e309d09189878a8887858c2748f0a0562e261e104e3245510910a8b0889068)))
def layer511r11 : Packing := (491,2,6,63,0,16,1,packed511r11)
def keys511k12 (i : Nat) : Nat := (if i < 1 then 0xd3148a625cac6d420007ed0de0503d68aa674916fd6d99c2591b307657768759973781189a400098bc0c9b38f01a26da315464f22a4000a81ef58e744c0221a9c1b31b172b1d50a7c93cb55c086411b62df57895800000029b0002c57ebc000089ba1e6a289ff3c0d34000855f3e4000000ed4225c000ea600010f87b039d2ef15d9b1db75e77952a428cbfd32d2da1d2008deeb0b18b57b882a6963b83255710504294b4726d29d27a012130aac036cc6f97d5696dfc3b2535e166080000000004b32d22c5d7d10e7e2b3d3ebe378ec38f43900077165bae9b45668e0a80680551c409a6ae99d1089b1f5c000a325e1b576000db509a4000be00002c8a2b700a0001039c954caacc8b384e2bcd96d569ab4926e5edad50ec82e33c655adcb39e985a6c983236d5b68fc34899e68717f13e4c20c26b288f483cc4713ccd6155450444a513775597455c893800077a7e1e41573d50918464671e2023f4984e566438892facc026262a6a7a8a416542e3dd7406f158fbb440bf3cd5ccd903e76730ae859ee778c83001cf7d6ca000000000072c38045b2ee84f3c4b933dde94f232b838700000010bc000796f49400191bcad7655187b1296215c400000019619825a72c66e8916d276e66d8c00029b068ff5ed27908ab4600000000004d654ee9fe335d8b57712480006c873e61d95497ce0a6c2700016090001240c5011a194f254f520000bb8c9d1538cb0000003f1e7e1076a9d52e5ae50a284314fc627fc4c69fe2211c6d8b2d402e000c20e324001d810000002b7338d0000000000594a4605a4adc000b12805b24196c11166fcf406ecbf2f53937a000000658846bfb0763e41febf1aca97dbaed1735357f80012a35e2d79e090b26d0e1c935b6024f417a805bcd9f674918ed7552dae187056ec15de32cb810160a2ad7ebfeccf2207abc9bd5780001ca169142a41fe44b6e675fe2877b00052184a0806f8b3a11dc830beb07caa3425df339beb5d6667dae98a0aa86ea7835e3e35ef8ba9c0094aa2bdc9a18110a4699214d9d51e768306995d8fc2ad1793ce652efd06fe17561bc690000e6d8010cf4000bdaed12dbfb90d7300029e95ea33de02e5136c162062820780009f38003a3c1cc38fe6be50e196c5ba06c00153818ee8e80016de0003a7e378d7d00003a2cf0bb600053d6dcfbc4aabb5f000681a000000346e0001403163d03100e000601111e02013000000a00001d04190a0600010e270023102e040000032542230a021b1962070610000d00020a0c08011d01000306172d090000010a15190b09000003121d2702020b6a0106000804290108100a9c0022060307071e000f35021b0100032d0301000100050006060000001903000a00010202084b0344010b00601c420003001008090f2004610c4a14080f0800010d034a07000d else 0xd47248fac3a62b3beef986c0f2c19c1234cf52e0419b8a9ece4900053f617cdd4700cf9b9a95d5236d8566e6e1f0000000)
def packed511r12 (i : Nat) : Nat := 0x9107a243962a3502018a88425c69cf44962a3109850803125c621389102a24329185d02844428405c69c48886125a18d38a104024b8d30a1220ec328105c6a4410880e5a08d383892e31094e0a1110194202e35228410080e5998d40910322433e2e350284443c405c69c509106219e082e35258508880cf10171a91210508890e5c6a221e290e58a111a81422210971a629125888c42614246c4866c5c6a050986125978d38a1042203971a71424444867a30ba050929121cb111a8890c54b8d2c1890c4cb8d344862e3490c24b8d20388425c696243171a4890c44b8d2eb6cff93f0c5dab475b29e4f798125e294147ace7dad3155aea6534a393f6710c694f2223a05c0960e812c14800ffe88ffd87ffc87ffe77ffd86ffd76ffd84ffd74ffd64ffd83ffd73ffd63ffd43ffd82ffd72ffd42ffd32ffd80ffc80ffd70ffc70ffd60ffd40ffd30ffd20ffe00bfe88dfe77efe66fbe44fde33fee22ffa00
def layer511r12 : Packing := (33,1,6,63,0,11,1,packed511r12)
def keys511k13 (i : Nat) : Nat := 0x420060029912c000000000194b159c00000000000021f40c0983f12b5400003d190800d3000003d30800d0018e001167740000000a0400000009008ae1c00f680005ed8c78000000000000000000015b000000000000210e1004c00
def packed511r13 (i : Nat) : Nat := 0x8196349ff
def layer511r13 : Packing := (1,0,6,63,0,0,1,packed511r13)
def samples511 : Array (Bits × Bits) := #[(0x2040604c03000f12ccc024000acc000cc00004101010591b009a5000270003fff0861c30c393e4000ffff3333cccc000fffffff,0x204401000512ccc024c09accc0accc0a000000000909000a5302a33028c0b0020c10009164c0a4c0b1111ccccc125554c13),(0x418080700cb32c0000fab8000cf0000f000008286860a024936c600039fffc00031860ccb2e338000c000ccccfffffffcccc000,0x80005004b32c00005ab9425cf1426f1426000828200000912c6509a9509d426108204cb2e339446d44644445555447cccd44a),(0x82231180100030a30f0cc0000f00000fffff30c1818cce38e38f80003e0000000c63870f3cfc3ffff0000f0f0f0f0000f0f0000,0x211080000000a3050cc009df0009e5409f1040808cce38e38f8047be047811e422850514b42c11f011ef0f0f0f0136f0f013a),(0x10404020260c3c0c3f00f00000ffffff00000c30e0e0f0fc0fc0fffffc00000000f83f80fc0ffc00000000ff00ff00000ff00000,0x220c140c3500f0007df5407f0007e410a0a050b40b40ef01fc001f807ef83f80fc0ffc00de00deff00ff000f6ff000fa),(0xffffffffffffffffffffffffe18381c0380fc00fc000ffffff00000000000fc0ff00ff000fff00000000000000ffc000fff00000000000ffff0000000fffffff,0x20828140280d400e4000fc81f60001f4001f4fc0ff00ff000fff000dd000dd0374ffc000fff00003d403d4eeee00003e4aaa83ec),(0xfffffffffffffffffffffffffe03fe003ff0000fffff00000000000000000fff0000fffff00000000000000000ffffff00000000000000fffffffffff0000000,0xfffffffffffffffffffffffffe03fe003fb0000ffffa0029d80029d8029d8fff0000fffff00000ad600ad62b58ef7dfb0000002b982b98bbbbaaaabb80002bb0),(0xfffffffffffffffffffffffffffc00003ffffff0000000000000000000000fffffff0000000000000000000000ffffffffffffffffffff000000000000000000,0xfffffffffffffffffffffffffffc00003fefffa0000000316000316003160efbf7f70000000000c9800c983260bdd72eaeb4a932e0b2e0000000032c000032c0),(0xffffffffffffffffffffffffffffffffc0000000000000000000000000000fffffffffffffffffffffffffffff00000000000000000000000000000000000000,0xfffffffffffffffffffffffffff7fdfa80000000000000218000218002180bef5d5daf4b64ad108e0148e0238000000000000023002300000000023000002300),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffdf7d6eb7d5f2abf18aaf037e000abe00abe0000000000000000000f0000f003c000000000000003c003c0000000003c000003c00)]
def cols511 : IndexTree ColumnInfo := (.fork 17 (.fork 8 (.fork 4 (.leaf [(0,32,477,2,12),(32,0,479,0,12),(4,0,507,0,11),(8,0,503,0,11)]) (.leaf [(16,0,495,0,11),(64,0,447,0,11),(2,32,477,0,11),(0,2,349,160,10)])) (.fork 4 (.leaf [(1,0,510,0,10),(128,0,383,0,10),(256,0,255,0,10),(68,0,443,0,10)]) (.fork 2 (.leaf [(0,4,187,320,9),(0,64,442,5,9)]) (.leaf [(8,2,341,160,9),(128,2,349,32,9),(136,0,375,0,9)])))) (.fork 8 (.fork 4 (.leaf [(0,8,119,384,8),(0,16,238,257,8),(0,256,227,28,8),(1,64,442,4,8)]) (.leaf [(4,64,442,1,8),(12,0,499,0,8),(17,0,494,0,8),(20,0,491,0,8)])) (.fork 4 (.leaf [(24,0,487,0,8),(64,4,187,256,8),(65,0,446,0,8),(72,0,439,0,8)]) (.fork 2 (.leaf [(80,0,431,0,8),(256,4,187,64,8)]) (.leaf [(260,0,251,0,8),(264,0,247,0,8),(272,0,239,0,8)])))))
def levels511 : Nat → Packing
  | 6 => layer511r6
  | 7 => layer511r7
  | 8 => layer511r8
  | 9 => layer511r9
  | 10 => layer511r10
  | 11 => layer511r11
  | 12 => layer511r12
  | 13 => layer511r13
  | _ => emptyPacking
def index511 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 keys511k7
  | 8 => lookupWord 1 4 0 5 1 0 keys511k8
  | 9 => lookupWord 16 59 5 10 6 0 keys511k9
  | 10 => lookupWord 212 724 8 14 10 0 keys511k10
  | 11 => lookupWord 706 2402 9 16 12 0 keys511k11
  | 12 => lookupWord 163 561 8 13 9 0 keys511k12
  | 13 => lookupWord 11 73 2 10 6 0 keys511k13
  | _ => fun _ => none
def g511 : Forest := ⟨511,13,fun j => samples511[j]?.getD (0,0),cols511,#[[]],levels511,index511,noFactory,noFactorySound 511⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom85 : graphValid g85 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice85k3p0 : block g85 3 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK85k3 : block g85 3 0 1=true := slice85k3p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked85 : checkedTables g85 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g85 0 0 0=true)
  · exact (rfl : block g85 1 0 0=true)
  · exact (rfl : block g85 2 0 0=true)
  · exact layerOK85k3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low85 : Lower (vars 85) (graphGoal 85) 4 :=
  lower_forest (g:=g85) (i:=0) (hints:=1540) (before_sound [] baseKnown) geom85 checked85 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps85 : List (Nat × List Nat) := [(85,[]),(153,[118,50]),(163,[118,84,16,32]),(170,[118,84,50,16]),(197,[116,84]),(201,[100,116,84,50]),(277,[128,112,96,64,32]),(325,[132,116,84,32]),(332,[134,100,116,84,32,48,16]),(337,[130,114,100,82,50]),(340,[134,100,116,66,82,32,48,16]),(393,[100,134,116,84,48,32]),(396,[134,116,84,48,16]),(408,[134,116,66,82,48,16])]
def known85 := extendKnown [] 4 maps85
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid85 : Known known85 := extendKnown_ok baseKnown low85 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom179 : graphValid g179 (boundsBefore known85) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice179k4p0 : block g179 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK179k4 : block g179 4 0 1=true := slice179k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked179 : checkedTables g179 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g179 0 0 0=true)
  · exact (rfl : block g179 1 0 0=true)
  · exact (rfl : block g179 2 0 0=true)
  · exact (rfl : block g179 3 0 0=true)
  · exact layerOK179k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low179 : Lower (vars 179) (graphGoal 179) 5 :=
  lower_forest (g:=g179) (i:=0) (hints:=1048660) (before_sound known85 valid85) geom179 checked179 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps179 : List (Nat × List Nat) := [(179,[]),(199,[97,49,50,82,65,112]),(205,[16,97,49,83,65,33,112]),(227,[100]),(333,[129,96,48,83,113,33,64]),(345,[129,65,97,116,81,49,33]),(397,[129,97,48,115,81,33,64]),(405,[129,97,116,81,33]),(426,[133,84,100,49,16,32]),(453,[116,133,100,33]),(457,[133,100,49,33]),(460,[117,133,100,49,32])]
def known179 := extendKnown known85 5 maps179
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid179 : Known known179 := extendKnown_ok valid85 low179 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom155 : graphValid g155 (boundsBefore known179) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice155k4p0 : block g155 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK155k4 : block g155 4 0 1=true := slice155k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked155 : checkedTables g155 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g155 0 0 0=true)
  · exact (rfl : block g155 1 0 0=true)
  · exact (rfl : block g155 2 0 0=true)
  · exact (rfl : block g155 3 0 0=true)
  · exact layerOK155k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low155 : Lower (vars 155) (graphGoal 155) 5 :=
  lower_forest (g:=g155) (i:=0) (hints:=28788) (before_sound known179 valid179) geom155 checked155 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps155 : List (Nat × List Nat) := [(171,[84,16]),(213,[48,99,83,65,33,112]),(217,[99,49,67,81,33,112]),(285,[135,33,64]),(348,[135,100,67,49,81,32]),(412,[116,132,100,67,48,16,81,32]),(465,[67,49,129,64,99,81,33,112])]
def known155 := extendKnown known179 5 maps155
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid155 : Known known155 := extendKnown_ok valid179 low155 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom341 : graphValid g341 (boundsBefore known155) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice341k5p0 : block g341 5 0 5 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice341k5p5 : block g341 5 5 10 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK341k5 : block g341 5 0 15=true := (@block_merge g341 5 0 5 10 slice341k5p0 slice341k5p5)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice341k6p0 : block g341 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK341k6 : block g341 6 0 1=true := slice341k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked341 : checkedTables g341 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g341 0 0 0=true)
  · exact (rfl : block g341 1 0 0=true)
  · exact (rfl : block g341 2 0 0=true)
  · exact (rfl : block g341 3 0 0=true)
  · exact (rfl : block g341 4 0 0=true)
  · exact layerOK341k5
  · exact layerOK341k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low341 : Lower (vars 341) (graphGoal 341) 7 :=
  lower_forest (g:=g341) (i:=0) (hints:=8589936132) (before_sound known155 valid155) geom341 checked341 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps341 : List (Nat × List Nat) := [(341,[]),(409,[118,50])]
def known341 := extendKnown known155 7 maps341
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid341 : Known known341 := extendKnown_ok valid155 low341 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom119 : graphValid g119 (boundsBefore known341) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice119k5p0 : block g119 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK119k5 : block g119 5 0 1=true := slice119k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked119 : checkedTables g119 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0=true)
  · exact (rfl : block g119 1 0 0=true)
  · exact (rfl : block g119 2 0 0=true)
  · exact (rfl : block g119 3 0 0=true)
  · exact (rfl : block g119 4 0 0=true)
  · exact layerOK119k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_forest (g:=g119) (i:=0) (hints:=1050196) (before_sound known341 valid341) geom119 checked119 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(238,[101,84,116,33,16,48]),(315,[128,112,96,64,48,32]),(359,[132,116,32]),(366,[134,100,116,32,48])]
def known119 := extendKnown known341 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid341 low119 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom231 : graphValid g231 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice231k6p0 : block g231 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK231k6 : block g231 6 0 1=true := slice231k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked231 : checkedTables g231 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0=true)
  · exact (rfl : block g231 1 0 0=true)
  · exact (rfl : block g231 2 0 0=true)
  · exact (rfl : block g231 3 0 0=true)
  · exact (rfl : block g231 4 0 0=true)
  · exact (rfl : block g231 5 0 0=true)
  · exact layerOK231k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low231 : Lower (vars 231) (graphGoal 231) 7 :=
  lower_forest (g:=g231) (i:=0) (hints:=1050198) (before_sound known119 valid119) geom231 checked231 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps231 : List (Nat × List Nat) := [(231,[]),(430,[134,48]),(435,[130,98,66,50]),(442,[134,66,48])]
def known231 := extendKnown known119 7 maps231
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid231 : Known known231 := extendKnown_ok valid119 low231 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom187 : graphValid g187 (boundsBefore known231) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice187k6p0 : block g187 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK187k6 : block g187 6 0 1=true := slice187k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked187 : checkedTables g187 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g187 0 0 0=true)
  · exact (rfl : block g187 1 0 0=true)
  · exact (rfl : block g187 2 0 0=true)
  · exact (rfl : block g187 3 0 0=true)
  · exact (rfl : block g187 4 0 0=true)
  · exact (rfl : block g187 5 0 0=true)
  · exact layerOK187k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low187 : Lower (vars 187) (graphGoal 187) 7 :=
  lower_forest (g:=g187) (i:=0) (hints:=1077332) (before_sound known231 valid231) geom187 checked187 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps187 : List (Nat × List Nat) := [(187,[]),(221,[16,97,49,83,65,33,112]),(235,[100]),(427,[133,84,100,16,48]),(459,[133,100,49]),(476,[117,133,67,49,97,32])]
def known187 := extendKnown known231 7 maps187
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid187 : Known known187 := extendKnown_ok valid231 low187 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom461 : graphValid g461 (boundsBefore known187) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice461k6p0 : block g461 6 0 6 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice461k6p6 : block g461 6 6 9 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK461k6 : block g461 6 0 15=true := (@block_merge g461 6 0 6 9 slice461k6p0 slice461k6p6)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice461k7p0 : block g461 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK461k7 : block g461 7 0 1=true := slice461k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked461 : checkedTables g461 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g461 0 0 0=true)
  · exact (rfl : block g461 1 0 0=true)
  · exact (rfl : block g461 2 0 0=true)
  · exact (rfl : block g461 3 0 0=true)
  · exact (rfl : block g461 4 0 0=true)
  · exact (rfl : block g461 5 0 0=true)
  · exact layerOK461k6
  · exact layerOK461k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low461 : Lower (vars 461) (graphGoal 461) 8 :=
  lower_forest (g:=g461) (i:=0) (hints:=8589964806) (before_sound known187 valid187) geom461 checked461 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps461 : List (Nat × List Nat) := [(461,[])]
def known461 := extendKnown known187 8 maps461
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid461 : Known known461 := extendKnown_ok valid187 low461 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom349 : graphValid g349 (boundsBefore known461) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice349k7p0 : block g349 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK349k7 : block g349 7 0 1=true := slice349k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked349 : checkedTables g349 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g349 0 0 0=true)
  · exact (rfl : block g349 1 0 0=true)
  · exact (rfl : block g349 2 0 0=true)
  · exact (rfl : block g349 3 0 0=true)
  · exact (rfl : block g349 4 0 0=true)
  · exact (rfl : block g349 5 0 0=true)
  · exact (rfl : block g349 6 0 0=true)
  · exact layerOK349k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low349 : Lower (vars 349) (graphGoal 349) 8 :=
  lower_forest (g:=g349) (i:=0) (hints:=8589968900) (before_sound known461 valid461) geom349 checked349 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps349 : List (Nat × List Nat) := [(349,[]),(411,[128,112,96,64,16,49,32]),(413,[118,50]),(469,[100,115,66,83,32,128]),(473,[99,116,66,48,82,128])]
def known349 := extendKnown known461 8 maps349
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid349 : Known known349 := extendKnown_ok valid461 low349 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom367 : graphValid g367 (boundsBefore known349) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice367k6p0 : block g367 6 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK367k6 : block g367 6 0 1=true := slice367k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked367 : checkedTables g367 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g367 0 0 0=true)
  · exact (rfl : block g367 1 0 0=true)
  · exact (rfl : block g367 2 0 0=true)
  · exact (rfl : block g367 3 0 0=true)
  · exact (rfl : block g367 4 0 0=true)
  · exact (rfl : block g367 5 0 0=true)
  · exact layerOK367k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low367 : Lower (vars 367) (graphGoal 367) 7 :=
  lower_forest (g:=g367) (i:=0) (hints:=8591017558) (before_sound known349 valid349) geom367 checked367 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps367 : List (Nat × List Nat) := [(367,[])]
def known367 := extendKnown known349 7 maps367
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid367 : Known known367 := extendKnown_ok valid349 low367 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom502 : graphValid g502 (boundsBefore known367) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice502k6p0 : block g502 6 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK502k6 : block g502 6 0 1=true := slice502k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked502 : checkedTables g502 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g502 0 0 0=true)
  · exact (rfl : block g502 1 0 0=true)
  · exact (rfl : block g502 2 0 0=true)
  · exact (rfl : block g502 3 0 0=true)
  · exact (rfl : block g502 4 0 0=true)
  · exact (rfl : block g502 5 0 0=true)
  · exact layerOK502k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low502 : Lower (vars 502) (graphGoal 502) 7 :=
  lower_forest (g:=g502) (i:=0) (hints:=8893498960) (before_sound known367 valid367) geom502 checked502 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps502 : List (Nat × List Nat) := [(502,[])]
def known502 := extendKnown known367 7 maps502
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid502 : Known known502 := extendKnown_ok valid367 low502 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom375 : graphValid g375 (boundsBefore known502) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice375k8p0 : block g375 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK375k8 : block g375 8 0 1=true := slice375k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked375 : checkedTables g375 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g375 0 0 0=true)
  · exact (rfl : block g375 1 0 0=true)
  · exact (rfl : block g375 2 0 0=true)
  · exact (rfl : block g375 3 0 0=true)
  · exact (rfl : block g375 4 0 0=true)
  · exact (rfl : block g375 5 0 0=true)
  · exact (rfl : block g375 6 0 0=true)
  · exact (rfl : block g375 7 0 0=true)
  · exact layerOK375k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low375 : Lower (vars 375) (graphGoal 375) 9 :=
  lower_forest (g:=g375) (i:=0) (hints:=8590984788) (before_sound known502 valid502) geom375 checked375 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps375 : List (Nat × List Nat) := [(375,[])]
def known375 := extendKnown known502 9 maps375
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid375 : Known known375 := extendKnown_ok valid502 low375 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom439 : graphValid g439 (boundsBefore known375) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice439k7p0 : block g439 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK439k7 : block g439 7 0 1=true := slice439k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked439 : checkedTables g439 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g439 0 0 0=true)
  · exact (rfl : block g439 1 0 0=true)
  · exact (rfl : block g439 2 0 0=true)
  · exact (rfl : block g439 3 0 0=true)
  · exact (rfl : block g439 4 0 0=true)
  · exact (rfl : block g439 5 0 0=true)
  · exact (rfl : block g439 6 0 0=true)
  · exact layerOK439k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low439 : Lower (vars 439) (graphGoal 439) 8 :=
  lower_forest (g:=g439) (i:=0) (hints:=8590985300) (before_sound known375 valid375) geom439 checked439 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps439 : List (Nat × List Nat) := [(439,[]),(487,[100,130]),(494,[66,100,130,48])]
def known439 := extendKnown known375 8 maps439
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid439 : Known known439 := extendKnown_ok valid375 low439 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom491 : graphValid g491 (boundsBefore known439) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice491k7p0 : block g491 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK491k7 : block g491 7 0 1=true := slice491k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked491 : checkedTables g491 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g491 0 0 0=true)
  · exact (rfl : block g491 1 0 0=true)
  · exact (rfl : block g491 2 0 0=true)
  · exact (rfl : block g491 3 0 0=true)
  · exact (rfl : block g491 4 0 0=true)
  · exact (rfl : block g491 5 0 0=true)
  · exact (rfl : block g491 6 0 0=true)
  · exact layerOK491k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low491 : Lower (vars 491) (graphGoal 491) 8 :=
  lower_forest (g:=g491) (i:=0) (hints:=12885979222) (before_sound known439 valid439) geom491 checked491 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps491 : List (Nat × List Nat) := [(491,[])]
def known491 := extendKnown known439 8 maps491
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid491 : Known known491 := extendKnown_ok valid439 low491 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom239 : graphValid g239 (boundsBefore known491) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice239k7p0 : block g239 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK239k7 : block g239 7 0 1=true := slice239k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked239 : checkedTables g239 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g239 0 0 0=true)
  · exact (rfl : block g239 1 0 0=true)
  · exact (rfl : block g239 2 0 0=true)
  · exact (rfl : block g239 3 0 0=true)
  · exact (rfl : block g239 4 0 0=true)
  · exact (rfl : block g239 5 0 0=true)
  · exact (rfl : block g239 6 0 0=true)
  · exact layerOK239k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low239 : Lower (vars 239) (graphGoal 239) 8 :=
  lower_forest (g:=g239) (i:=0) (hints:=1078870) (before_sound known491 valid491) geom239 checked239 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps239 : List (Nat × List Nat) := [(239,[]),(247,[67,82,97,112]),(431,[134,48]),(478,[118,101,133,48,33,64]),(499,[83,82,33,131,66,97,112])]
def known239 := extendKnown known491 8 maps239
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid239 : Known known239 := extendKnown_ok valid491 low239 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom446 : graphValid g446 (boundsBefore known239) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice446k7p0 : block g446 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK446k7 : block g446 7 0 1=true := slice446k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked446 : checkedTables g446 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g446 0 0 0=true)
  · exact (rfl : block g446 1 0 0=true)
  · exact (rfl : block g446 2 0 0=true)
  · exact (rfl : block g446 3 0 0=true)
  · exact (rfl : block g446 4 0 0=true)
  · exact (rfl : block g446 5 0 0=true)
  · exact (rfl : block g446 6 0 0=true)
  · exact layerOK446k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low446 : Lower (vars 446) (graphGoal 446) 8 :=
  lower_forest (g:=g446) (i:=0) (hints:=8859973712) (before_sound known239 valid239) geom446 checked446 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps446 : List (Nat × List Nat) := [(446,[])]
def known446 := extendKnown known239 8 maps446
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid446 : Known known446 := extendKnown_ok valid239 low446 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom223 : graphValid g223 (boundsBefore known446) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k7p0 : block g223 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK223k7 : block g223 7 0 1=true := slice223k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked223 : checkedTables g223 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g223 0 0 0=true)
  · exact (rfl : block g223 1 0 0=true)
  · exact (rfl : block g223 2 0 0=true)
  · exact (rfl : block g223 3 0 0=true)
  · exact (rfl : block g223 4 0 0=true)
  · exact (rfl : block g223 5 0 0=true)
  · exact (rfl : block g223 6 0 0=true)
  · exact layerOK223k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low223 : Lower (vars 223) (graphGoal 223) 8 :=
  lower_forest (g:=g223) (i:=0) (hints:=30324) (before_sound known446 valid446) geom223 checked223 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps223 : List (Nat × List Nat) := [(223,[]),(251,[49,67,82,97,112])]
def known223 := extendKnown known446 8 maps223
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid223 : Known known223 := extendKnown_ok valid446 low223 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom443 : graphValid g443 (boundsBefore known223) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice443k7p0 : block g443 7 0 10 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice443k7p10 : block g443 7 10 6 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK443k7 : block g443 7 0 16=true := (@block_merge g443 7 0 10 6 slice443k7p0 slice443k7p10)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice443k8p0 : block g443 8 0 5 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice443k8p5 : block g443 8 5 11 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK443k8 : block g443 8 0 16=true := (@block_merge g443 8 0 5 11 slice443k8p0 slice443k8p5)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice443k9p0 : block g443 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK443k9 : block g443 9 0 1=true := slice443k9p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked443 : checkedTables g443 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g443 0 0 0=true)
  · exact (rfl : block g443 1 0 0=true)
  · exact (rfl : block g443 2 0 0=true)
  · exact (rfl : block g443 3 0 0=true)
  · exact (rfl : block g443 4 0 0=true)
  · exact (rfl : block g443 5 0 0=true)
  · exact (rfl : block g443 6 0 0=true)
  · exact layerOK443k7
  · exact layerOK443k8
  · exact layerOK443k9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low443 : Lower (vars 443) (graphGoal 443) 10 :=
  lower_forest (g:=g443) (i:=0) (hints:=12885979220) (before_sound known223 valid223) geom443 checked443 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps443 : List (Nat × List Nat) := [(443,[]),(471,[16,97,50,66,81,112])]
def known443 := extendKnown known223 10 maps443
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid443 : Known known443 := extendKnown_ok valid223 low443 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom463 : graphValid g463 (boundsBefore known443) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice463k8p0 : block g463 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK463k8 : block g463 8 0 1=true := slice463k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked463 : checkedTables g463 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g463 0 0 0=true)
  · exact (rfl : block g463 1 0 0=true)
  · exact (rfl : block g463 2 0 0=true)
  · exact (rfl : block g463 3 0 0=true)
  · exact (rfl : block g463 4 0 0=true)
  · exact (rfl : block g463 5 0 0=true)
  · exact (rfl : block g463 6 0 0=true)
  · exact (rfl : block g463 7 0 0=true)
  · exact layerOK463k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low463 : Lower (vars 463) (graphGoal 463) 9 :=
  lower_forest (g:=g463) (i:=0) (hints:=8589964918) (before_sound known443 valid443) geom463 checked463 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps463 : List (Nat × List Nat) := [(463,[])]
def known463 := extendKnown known443 9 maps463
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid463 : Known known463 := extendKnown_ok valid443 low463 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom477 : graphValid g477 (boundsBefore known463) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice477k6p0 : block g477 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice477k6p1 : block g477 6 1 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK477k6 : block g477 6 0 2=true := (@block_merge g477 6 0 1 1 slice477k6p0 slice477k6p1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice477k7p0 : block g477 7 0 43 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice477k7p43 : block g477 7 43 44 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK477k7 : block g477 7 0 87=true := (@block_merge g477 7 0 43 44 slice477k7p0 slice477k7p43)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice477k8p0 : block g477 8 0 20 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice477k8p20 : block g477 8 20 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice477k8p84 : block g477 8 84 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice477k8p148 : block g477 8 148 60 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice477k8p208 : block g477 8 208 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice477k8p272 : block g477 8 272 39 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK477k8 : block g477 8 0 311=true := (@block_merge g477 8 0 272 39 (@block_merge g477 8 0 208 64 (@block_merge g477 8 0 148 60 (@block_merge g477 8 0 84 64 (@block_merge g477 8 0 20 64 slice477k8p0 slice477k8p20) slice477k8p84) slice477k8p148) slice477k8p208) slice477k8p272)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice477k9p0 : block g477 9 0 7 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice477k9p7 : block g477 9 7 22 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK477k9 : block g477 9 0 29=true := (@block_merge g477 9 0 7 22 slice477k9p0 slice477k9p7)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice477k10p0 : block g477 10 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK477k10 : block g477 10 0 1=true := slice477k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked477 : checkedTables g477 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g477 0 0 0=true)
  · exact (rfl : block g477 1 0 0=true)
  · exact (rfl : block g477 2 0 0=true)
  · exact (rfl : block g477 3 0 0=true)
  · exact (rfl : block g477 4 0 0=true)
  · exact (rfl : block g477 5 0 0=true)
  · exact layerOK477k6
  · exact layerOK477k7
  · exact layerOK477k8
  · exact layerOK477k9
  · exact layerOK477k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low477 : Lower (vars 477) (graphGoal 477) 11 :=
  lower_forest (g:=g477) (i:=0) (hints:=8589964804) (before_sound known463 valid463) geom477 checked477 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps477 : List (Nat × List Nat) := [(477,[])]
def known477 := extendKnown known463 11 maps477
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid477 : Known known477 := extendKnown_ok valid463 low477 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known477) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice383k9p0 : block g383 9 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK383k9 : block g383 9 0 1=true := slice383k9p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked383 : checkedTables g383 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0=true)
  · exact (rfl : block g383 1 0 0=true)
  · exact (rfl : block g383 2 0 0=true)
  · exact (rfl : block g383 3 0 0=true)
  · exact (rfl : block g383 4 0 0=true)
  · exact (rfl : block g383 5 0 0=true)
  · exact (rfl : block g383 6 0 0=true)
  · exact (rfl : block g383 7 0 0=true)
  · exact (rfl : block g383 8 0 0=true)
  · exact layerOK383k9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 10 :=
  lower_forest (g:=g383) (i:=0) (hints:=8591017556) (before_sound known477 valid477) geom383 checked383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[])]
def known383 := extendKnown known477 10 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid477 low383 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom510 : graphValid g510 (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice510k8p0 : block g510 8 0 4 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice510k8p4 : block g510 8 4 1 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK510k8 : block g510 8 0 5=true := (@block_merge g510 8 0 4 1 slice510k8p0 slice510k8p4)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice510k9p0 : block g510 9 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK510k9 : block g510 9 0 1=true := slice510k9p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked510 : checkedTables g510 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g510 0 0 0=true)
  · exact (rfl : block g510 1 0 0=true)
  · exact (rfl : block g510 2 0 0=true)
  · exact (rfl : block g510 3 0 0=true)
  · exact (rfl : block g510 4 0 0=true)
  · exact (rfl : block g510 5 0 0=true)
  · exact (rfl : block g510 6 0 0=true)
  · exact (rfl : block g510 7 0 0=true)
  · exact layerOK510k8
  · exact layerOK510k9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low510 : Lower (vars 510) (graphGoal 510) 10 :=
  lower_forest (g:=g510) (i:=0) (hints:=8893527632) (before_sound known383 valid383) geom510 checked510 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps510 : List (Nat × List Nat) := [(510,[])]
def known510 := extendKnown known383 10 maps510
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid510 : Known known510 := extendKnown_ok valid383 low510 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom255 : graphValid g255 (boundsBefore known510) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p0 : block g255 8 0 4 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p4 : block g255 8 4 1 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k8 : block g255 8 0 5=true := (@block_merge g255 8 0 4 1 slice255k8p0 slice255k8p4)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p0 : block g255 9 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k9 : block g255 9 0 1=true := slice255k9p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked255 : checkedTables g255 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0=true)
  · exact (rfl : block g255 1 0 0=true)
  · exact (rfl : block g255 2 0 0=true)
  · exact (rfl : block g255 3 0 0=true)
  · exact (rfl : block g255 4 0 0=true)
  · exact (rfl : block g255 5 0 0=true)
  · exact (rfl : block g255 6 0 0=true)
  · exact (rfl : block g255 7 0 0=true)
  · exact layerOK255k8
  · exact layerOK255k9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 10 :=
  lower_forest (g:=g255) (i:=0) (hints:=1078868) (before_sound known510 valid510) geom255 checked255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[])]
def known255 := extendKnown known510 10 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid510 low255 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom503 : graphValid g503 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k10p0 : block g503 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK503k10 : block g503 10 0 1=true := slice503k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked503 : checkedTables g503 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g503 0 0 0=true)
  · exact (rfl : block g503 1 0 0=true)
  · exact (rfl : block g503 2 0 0=true)
  · exact (rfl : block g503 3 0 0=true)
  · exact (rfl : block g503 4 0 0=true)
  · exact (rfl : block g503 5 0 0=true)
  · exact (rfl : block g503 6 0 0=true)
  · exact (rfl : block g503 7 0 0=true)
  · exact (rfl : block g503 8 0 0=true)
  · exact (rfl : block g503 9 0 0=true)
  · exact layerOK503k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low503 : Lower (vars 503) (graphGoal 503) 11 :=
  lower_forest (g:=g503) (i:=0) (hints:=8590984788) (before_sound known255 valid255) geom503 checked503 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps503 : List (Nat × List Nat) := [(503,[])]
def known503 := extendKnown known255 11 maps503
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid503 : Known known503 := extendKnown_ok valid255 low503 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom495 : graphValid g495 (boundsBefore known503) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice495k8p0 : block g495 8 0 11 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice495k8p11 : block g495 8 11 4 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK495k8 : block g495 8 0 15=true := (@block_merge g495 8 0 11 4 slice495k8p0 slice495k8p11)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice495k9p0 : block g495 9 0 6 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice495k9p6 : block g495 9 6 12 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK495k9 : block g495 9 0 18=true := (@block_merge g495 9 0 6 12 slice495k9p0 slice495k9p6)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice495k10p0 : block g495 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK495k10 : block g495 10 0 1=true := slice495k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked495 : checkedTables g495 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g495 0 0 0=true)
  · exact (rfl : block g495 1 0 0=true)
  · exact (rfl : block g495 2 0 0=true)
  · exact (rfl : block g495 3 0 0=true)
  · exact (rfl : block g495 4 0 0=true)
  · exact (rfl : block g495 5 0 0=true)
  · exact (rfl : block g495 6 0 0=true)
  · exact (rfl : block g495 7 0 0=true)
  · exact layerOK495k8
  · exact layerOK495k9
  · exact layerOK495k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low495 : Lower (vars 495) (graphGoal 495) 11 :=
  lower_forest (g:=g495) (i:=0) (hints:=8591013462) (before_sound known503 valid503) geom495 checked495 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps495 : List (Nat × List Nat) := [(495,[])]
def known495 := extendKnown known503 11 maps495
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid495 : Known known495 := extendKnown_ok valid503 low495 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom507 : graphValid g507 (boundsBefore known495) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k10p0 : block g507 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK507k10 : block g507 10 0 1=true := slice507k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked507 : checkedTables g507 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g507 0 0 0=true)
  · exact (rfl : block g507 1 0 0=true)
  · exact (rfl : block g507 2 0 0=true)
  · exact (rfl : block g507 3 0 0=true)
  · exact (rfl : block g507 4 0 0=true)
  · exact (rfl : block g507 5 0 0=true)
  · exact (rfl : block g507 6 0 0=true)
  · exact (rfl : block g507 7 0 0=true)
  · exact (rfl : block g507 8 0 0=true)
  · exact (rfl : block g507 9 0 0=true)
  · exact layerOK507k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low507 : Lower (vars 507) (graphGoal 507) 11 :=
  lower_forest (g:=g507) (i:=0) (hints:=12885979220) (before_sound known495 valid495) geom507 checked507 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps507 : List (Nat × List Nat) := [(507,[])]
def known507 := extendKnown known495 11 maps507
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid507 : Known known507 := extendKnown_ok valid495 low507 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom447 : graphValid g447 (boundsBefore known507) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice447k10p0 : block g447 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK447k10 : block g447 10 0 1=true := slice447k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked447 : checkedTables g447 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g447 0 0 0=true)
  · exact (rfl : block g447 1 0 0=true)
  · exact (rfl : block g447 2 0 0=true)
  · exact (rfl : block g447 3 0 0=true)
  · exact (rfl : block g447 4 0 0=true)
  · exact (rfl : block g447 5 0 0=true)
  · exact (rfl : block g447 6 0 0=true)
  · exact (rfl : block g447 7 0 0=true)
  · exact (rfl : block g447 8 0 0=true)
  · exact (rfl : block g447 9 0 0=true)
  · exact layerOK447k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low447 : Lower (vars 447) (graphGoal 447) 11 :=
  lower_forest (g:=g447) (i:=0) (hints:=8591013972) (before_sound known507 valid507) geom447 checked447 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps447 : List (Nat × List Nat) := [(447,[])]
def known447 := extendKnown known507 11 maps447
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid447 : Known known447 := extendKnown_ok valid507 low447 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom479 : graphValid g479 (boundsBefore known447) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice479k11p0 : block g479 11 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK479k11 : block g479 11 0 1=true := slice479k11p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked479 : checkedTables g479 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g479 0 0 0=true)
  · exact (rfl : block g479 1 0 0=true)
  · exact (rfl : block g479 2 0 0=true)
  · exact (rfl : block g479 3 0 0=true)
  · exact (rfl : block g479 4 0 0=true)
  · exact (rfl : block g479 5 0 0=true)
  · exact (rfl : block g479 6 0 0=true)
  · exact (rfl : block g479 7 0 0=true)
  · exact (rfl : block g479 8 0 0=true)
  · exact (rfl : block g479 9 0 0=true)
  · exact (rfl : block g479 10 0 0=true)
  · exact layerOK479k11
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low479 : Lower (vars 479) (graphGoal 479) 12 :=
  lower_forest (g:=g479) (i:=0) (hints:=8589964916) (before_sound known447 valid447) geom479 checked479 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps479 : List (Nat × List Nat) := [(479,[])]
def known479 := extendKnown known447 12 maps479
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid479 : Known known479 := extendKnown_ok valid447 low479 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom511 : graphValid g511 (boundsBefore known479) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k6p0 : block g511 6 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k6 : block g511 6 0 1=true := slice511k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k7p0 : block g511 7 0 2 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k7 : block g511 7 0 2=true := slice511k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k8p0 : block g511 8 0 19 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k8p19 : block g511 8 19 29 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k8 : block g511 8 0 48=true := (@block_merge g511 8 0 19 29 slice511k8p0 slice511k8p19)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p0 : block g511 9 0 3 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p3 : block g511 9 3 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p67 : block g511 9 67 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p131 : block g511 9 131 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p195 : block g511 9 195 13 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p208 : block g511 9 208 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p272 : block g511 9 272 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p336 : block g511 9 336 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p400 : block g511 9 400 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p464 : block g511 9 464 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p528 : block g511 9 528 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p592 : block g511 9 592 46 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k9 : block g511 9 0 638=true := (@block_merge g511 9 0 592 46 (@block_merge g511 9 0 528 64 (@block_merge g511 9 0 464 64 (@block_merge g511 9 0 400 64 (@block_merge g511 9 0 336 64 (@block_merge g511 9 0 272 64 (@block_merge g511 9 0 208 64 (@block_merge g511 9 0 195 13 (@block_merge g511 9 0 131 64 (@block_merge g511 9 0 67 64 (@block_merge g511 9 0 3 64 slice511k9p0 slice511k9p3) slice511k9p67) slice511k9p131) slice511k9p195) slice511k9p208) slice511k9p272) slice511k9p336) slice511k9p400) slice511k9p464) slice511k9p528) slice511k9p592)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p0 : block g511 10 0 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p64 : block g511 10 64 22 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p86 : block g511 10 86 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p150 : block g511 10 150 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p214 : block g511 10 214 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p278 : block g511 10 278 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p342 : block g511 10 342 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p406 : block g511 10 406 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p470 : block g511 10 470 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p534 : block g511 10 534 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p598 : block g511 10 598 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p662 : block g511 10 662 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p726 : block g511 10 726 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p790 : block g511 10 790 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p854 : block g511 10 854 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p918 : block g511 10 918 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p982 : block g511 10 982 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p1046 : block g511 10 1046 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p1110 : block g511 10 1110 36 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p1146 : block g511 10 1146 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p1210 : block g511 10 1210 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p1274 : block g511 10 1274 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p1338 : block g511 10 1338 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p1402 : block g511 10 1402 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p1466 : block g511 10 1466 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p1530 : block g511 10 1530 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p1594 : block g511 10 1594 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p1658 : block g511 10 1658 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p1722 : block g511 10 1722 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p1786 : block g511 10 1786 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p1850 : block g511 10 1850 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p1914 : block g511 10 1914 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p1978 : block g511 10 1978 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p2042 : block g511 10 2042 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p2106 : block g511 10 2106 13 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k10 : block g511 10 0 2119=true := (@block_merge g511 10 0 2106 13 (@block_merge g511 10 0 2042 64 (@block_merge g511 10 0 1978 64 (@block_merge g511 10 0 1914 64 (@block_merge g511 10 0 1850 64 (@block_merge g511 10 0 1786 64 (@block_merge g511 10 0 1722 64 (@block_merge g511 10 0 1658 64 (@block_merge g511 10 0 1594 64 (@block_merge g511 10 0 1530 64 (@block_merge g511 10 0 1466 64 (@block_merge g511 10 0 1402 64 (@block_merge g511 10 0 1338 64 (@block_merge g511 10 0 1274 64 (@block_merge g511 10 0 1210 64 (@block_merge g511 10 0 1146 64 (@block_merge g511 10 0 1110 36 (@block_merge g511 10 0 1046 64 (@block_merge g511 10 0 982 64 (@block_merge g511 10 0 918 64 (@block_merge g511 10 0 854 64 (@block_merge g511 10 0 790 64 (@block_merge g511 10 0 726 64 (@block_merge g511 10 0 662 64 (@block_merge g511 10 0 598 64 (@block_merge g511 10 0 534 64 (@block_merge g511 10 0 470 64 (@block_merge g511 10 0 406 64 (@block_merge g511 10 0 342 64 (@block_merge g511 10 0 278 64 (@block_merge g511 10 0 214 64 (@block_merge g511 10 0 150 64 (@block_merge g511 10 0 86 64 (@block_merge g511 10 0 64 22 slice511k10p0 slice511k10p64) slice511k10p86) slice511k10p150) slice511k10p214) slice511k10p278) slice511k10p342) slice511k10p406) slice511k10p470) slice511k10p534) slice511k10p598) slice511k10p662) slice511k10p726) slice511k10p790) slice511k10p854) slice511k10p918) slice511k10p982) slice511k10p1046) slice511k10p1110) slice511k10p1146) slice511k10p1210) slice511k10p1274) slice511k10p1338) slice511k10p1402) slice511k10p1466) slice511k10p1530) slice511k10p1594) slice511k10p1658) slice511k10p1722) slice511k10p1786) slice511k10p1850) slice511k10p1914) slice511k10p1978) slice511k10p2042) slice511k10p2106)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p0 : block g511 11 0 30 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p30 : block g511 11 30 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p94 : block g511 11 94 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p158 : block g511 11 158 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p222 : block g511 11 222 53 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p275 : block g511 11 275 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p339 : block g511 11 339 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p403 : block g511 11 403 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p467 : block g511 11 467 24 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k11 : block g511 11 0 491=true := (@block_merge g511 11 0 467 24 (@block_merge g511 11 0 403 64 (@block_merge g511 11 0 339 64 (@block_merge g511 11 0 275 64 (@block_merge g511 11 0 222 53 (@block_merge g511 11 0 158 64 (@block_merge g511 11 0 94 64 (@block_merge g511 11 0 30 64 slice511k11p0 slice511k11p30) slice511k11p94) slice511k11p158) slice511k11p222) slice511k11p275) slice511k11p339) slice511k11p403) slice511k11p467)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k12p0 : block g511 12 0 7 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k12p7 : block g511 12 7 26 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k12 : block g511 12 0 33=true := (@block_merge g511 12 0 7 26 slice511k12p0 slice511k12p7)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k13p0 : block g511 13 0 1 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k13 : block g511 13 0 1=true := slice511k13p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked511 : checkedTables g511 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g511 0 0 0=true)
  · exact (rfl : block g511 1 0 0=true)
  · exact (rfl : block g511 2 0 0=true)
  · exact (rfl : block g511 3 0 0=true)
  · exact (rfl : block g511 4 0 0=true)
  · exact (rfl : block g511 5 0 0=true)
  · exact layerOK511k6
  · exact layerOK511k7
  · exact layerOK511k8
  · exact layerOK511k9
  · exact layerOK511k10
  · exact layerOK511k11
  · exact layerOK511k12
  · exact layerOK511k13
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low511 : Lower (vars 511) (graphGoal 511) 14 :=
  lower_forest (g:=g511) (i:=0) (hints:=8591013460) (before_sound known479 valid479) geom511 checked511 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps511 : List (Nat × List Nat) := [(511,[])]
def known511 := extendKnown known479 14 maps511
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid511 : Known known511 := extendKnown_ok valid479 low511 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exactLower : ∀ t, PEqualNP.MetaComplexity.HasCircuitSize 9 edge9411 t → 14 ≤ t :=
  conclude9411 (root_index (g:=g511) (before_sound known479 valid479) geom511 checked511 (k:=13) (by decide) (i:=0) (by decide +kernel))

end PEqualNP.Outside.L_meta_9409

theorem PEqualNP.Outside.L_meta_9409 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 4 && x 8)) t → 14 ≤ t := PEqualNP.Outside.L_meta_9409.exactLower

import PEqualNP.Defs

-- The Live/Run/Forest checker derives from PressF10, pequalnp-proofs PR 4332,
-- and its extension in L_meta_3853, licensed under Apache-2.0.
namespace PEqualNP.Outside.L_meta_8443
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
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 6) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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


abbrev Bits := BitVec 256
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 256 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 256 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 256 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 256 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 256 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 256 → Row) (d : Bool) (a b : Sig) :
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

def asRow (cols : Nat → Bits) (i : Fin 256) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 256) (j : Fin 9) :
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
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 6) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 256) (j : Fin 9) :
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
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 256) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide)]
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
    if (rs ||| column d z.2) != BitVec.allOnes 256 then true else
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
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 256 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 256) = false := by simp [sep]
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 256) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val :=
  bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 256) (hq : chartSamples m q = 0) :
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 256) &&
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
def lanePlace (v : Nat) (upper : Nat) := 2^257*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^257 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<257 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<257 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<257 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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

def fullMarks (r packed : Nat) := ((packed+r) >>> 256) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (257*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^257)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 257*(i+1)-257=257*i := by omega
      have ge : ¬257*(i+1)<257 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 256 = (a==BitVec.allOnes 256) := by
  by_cases h : a=BitVec.allOnes 256
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^256-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^256 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (257*i) =
      (f xs[i]==BitVec.allOnes 256) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^257*u+x+(2^257*v+1)=2^257*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^257 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬257*(i+1)+256<257 := by omega
      have di : 257*(i+1)+256-257=257*i+256 := by omega
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
theorem top_xor (a : Bits) : BitVec.allOnes 256 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 256).toNat) op
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 257) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (257*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 257) (i:=i) (by simpa using hi) _ ok.2
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
    let z := packedOp (r*(BitVec.allOnes 256).toNat) op a b'
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
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 256 then true
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
        packedColumn d (packedOp (r*(BitVec.allOnes 256).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 256
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

def edge8444 : (Fin 8 → Bool) → Bool := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)
def sample8444 (r : Row) (i : Fin 8) := bit r (inputs.getD i.val zero)
theorem raw8444 : List.ofFn (fun i : Fin 8 => inputs.getD i.val zero) = vars 255 := by decide +kernel
theorem samples8444 (r : Row) : List.ofFn (sample8444 r) = (vars 255).map (bit r) := by
  rw [←raw8444,List.map_ofFn]
  rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem edge8444_table : ∀ r : Row, bit r (graphGoal 255) = edge8444 (sample8444 r) := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem conclude8444 (absent : Impossible (graphGoal 255) 12 (vars 255).toFinset) :
    ∀ t, PEqualNP.MetaComplexity.HasCircuitSize 8 edge8444 t → 13 ≤ t := by
  intro t hs
  obtain ⟨C,hf,hsize,correct⟩ := hs
  by_contra! bad
  have hp : proper (graphGoal 255) := by unfold proper; decide +kernel
  have he : (execute C.gates (vars 255)).getD C.output zero = graphGoal 255 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute C.gates (vars 255)).getD C.output zero) = bit r (graphGoal 255)
    rw [←b_read,execute_bits _ _ _ (fun g hg => (hf g hg).1),←samples8444,edge8444_table]
    exact correct (sample8444 r)
  have hout := get_rep (execute C.gates (vars 255)) C.output
  rw [he] at hout
  obtain ⟨k,u,S,hk,run,sub⟩ := extract C.gates _ hf hp (hout.resolve_right (fun h => h hp))
  have all : ∀ a ∈ vars 255, Essential (graphGoal 255) (vars 255) a := by
    have valid : checkEssential (graphGoal 255) (vars 255) (graphPairs 255 839974913) = true := by decide +kernel
    have ident : (graphPairs 255 839974913).map Prod.fst = vars 255 := by decide +kernel
    intro a ha
    apply essential_ok valid a
    rw [ident]
    exact List.mem_toFinset.mpr ha
  have eq : S=(vars 255).toFinset := by
    ext a
    constructor
    · exact fun ha => List.mem_toFinset.mpr (sub a ha)
    · intro ha
      obtain ⟨r,s,diff,sep⟩ := all a (List.mem_toFinset.mp ha)
      exact raw_required run _ a sub r s diff sep
  rw [eq] at run
  change C.gates.length ≤ t at hsize
  exact absent k u (by omega) run
def packed23r3 (i : Nat) : Nat := 0xf
def layer23r3 : Packing := (1,0,0,63,0,0,1,packed23r3)
def samples23 : Array (Bits × Bits) := #[(0x707ff,0x34129),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9fc1f,0x81c86),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe07e0,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc96d4),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7e318),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols23 : IndexTree ColumnInfo := (.leaf [])
def levels23 : Nat → Packing
  | 3 => layer23r3
  | _ => emptyPacking
def index23 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g23 : Forest := ⟨23,3,fun j => samples23[j]?.getD (0,0),cols23,#[[]],levels23,index23,noFactory,noFactorySound 23⟩
def packed91r4 (i : Nat) : Nat := 0x1f
def layer91r4 : Packing := (1,0,0,63,0,0,1,packed91r4)
def samples91 : Array (Bits × Bits) := #[(0x181f381fff,0x1a451a8555),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffff2013cff03f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffff2412443822),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffc01cf01fc0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffc498e51aa8),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0ffe000,0x48e0b9c30c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffb71f060c30),(0x0,0x0),(0x0,0x0)]
def cols91 : IndexTree ColumnInfo := (.leaf [])
def levels91 : Nat → Packing
  | 4 => layer91r4
  | _ => emptyPacking
def index91 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g91 : Forest := ⟨91,4,fun j => samples91[j]?.getD (0,0),cols91,#[[]],levels91,index91,noFactory,noFactorySound 91⟩
def packed31r4 (i : Nat) : Nat := 0x3f
def layer31r4 : Packing := (1,0,0,63,0,0,1,packed31r4)
def samples31 : Array (Bits × Bits) := #[(0x26707ffff,0x23404929),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffd99fd041f,0x4881d2486),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffe1e0607e0,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffe1c96a6d4),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffe007f800,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffc097b294),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffb77e0c318),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols31 : IndexTree ColumnInfo := (.leaf [(4,0,27,0,4)])
def levels31 : Nat → Packing
  | 4 => layer31r4
  | _ => emptyPacking
def index31 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g31 : Forest := ⟨31,4,fun j => samples31[j]?.getD (0,0),cols31,#[[]],levels31,index31,noFactory,noFactorySound 31⟩
def packed87r5 (i : Nat) : Nat := 0x202608000902208000020080200803f3b6cc5729487ce19283c50500fd43fd42fd32fd41fd31fd21fd40fd30fd20fd10be44de33ee22f611fa00
def layer87r5 : Packing := (15,1,3,63,0,7,1,packed87r5)
def keys87k6 (i : Nat) : Nat := 0x67000000418300004ec20012eb8e0071000de8f51ce004005200
def packed87r6 (i : Nat) : Nat := 0x23444bf
def layer87r6 : Packing := (1,0,3,63,0,0,1,packed87r6)
def samples87 : Array (Bits × Bits) := #[(0xc01019c07fff,0xd21488d414a9),(0x100601e7fc07f,0x120e85221e246),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffe007fe7807f80,0xfffffffffffffffffffffffffffffffffffffffffffffffffffe04a167094b14),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffff8007ff8000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffe470185ce0c18),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000,0x1b85e18303060),(0x0,0x0),(0x0,0x0)]
def cols87 : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,86,0,4),(2,0,85,0,4)]) (.leaf [(4,0,83,0,4),(16,0,71,0,4),(64,0,23,0,4)]))
def levels87 : Nat → Packing
  | 5 => layer87r5
  | 6 => layer87r6
  | _ => emptyPacking
def index87 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 5 25 3 8 4 0 keys87k6
  | _ => fun _ => none
def g87 : Forest := ⟨87,6,fun j => samples87[j]?.getD (0,0),cols87,#[[]],levels87,index87,noFactory,noFactorySound 87⟩
def packed111r6 (i : Nat) : Nat := 0x90ff
def layer111r6 : Packing := (1,0,2,63,0,0,1,packed111r6)
def samples111 : Array (Bits × Bits) := #[(0x720720326701ffffff,0x3201281023401090a1),(0x183e4c03d99ff40407f,0x80e4c4a488274a4a16),(0xfffffffffffffffffffffffffffffffffffffffffffffe1c78ffce1e01807f80,0x2042841ce1c1586470c),(0xffffffffffffffffffffffffffffffffffffffffffffffe07f000fe001ff8000,0xffffffffffffffffffffffffffffffffffffffffffffffc07e158fc0b5ef2e5c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffff80000ffffe000000,0xffffffffffffffffffffffffffffffffffffffffffffff7f00190b77d8343468),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000,0xfffffffffffffffffffffffffffffffffffffffffffffdfbd7be3000e0383870),(0x0,0x0),(0x0,0x0)]
def cols111 : IndexTree ColumnInfo := (.leaf [(8,0,103,0,5),(2,32,77,0,4),(4,64,43,0,4)])
def levels111 : Nat → Packing
  | 6 => layer111r6
  | _ => emptyPacking
def index111 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => samples111[j]?.getD (0,0),cols111,#[[]],levels111,index111,noFactory,noFactorySound 111⟩
def packed219r6 (i : Nat) : Nat := 0x404a08000c100220400820040080100200400c5c03d3a34af29a6a11b96108b05807f54ffa85fd32fea8ff507fa43fd50fea07f4c2fcabbe44ef19fb88bec23fa00
def layer219r6 : Packing := (15,1,4,63,0,8,1,packed219r6)
def keys219k7 (i : Nat) : Nat := 0x1d801c00193ce1400039eb2b7ba2c0aa660000000690403
def packed219r7 (i : Nat) : Nat := 0xb87a969bf
def layer219r7 : Packing := (1,0,4,63,0,0,1,packed219r7)
def samples219 : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffe0c048406180f9c07fff,0xffffffffffffffffffffffffffffffffffffffffffffe0e2486221c828e424c9),(0xb000f8072009e7fc07f,0xb14039452309218d832),(0x0,0x0),(0xc0071ff9c00e7807f80,0xc0490859c12c70a4b14),(0xfffffffffffffffffffffffffffffffffffffffffffff0007e001fff07ff8000,0xfffffffffffffffffffffffffffffffffffffffffffff020fc2104c305e32244),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffff80001ffff8000000,0xd4700061b1cf80c0c18),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000,0xfffffffffffffffffffffffffffffffffffffffffffff2b86f78606000303060),(0x0,0x0)]
def cols219 : IndexTree ColumnInfo := (.fork 6 (.fork 3 (.leaf [(1,0,218,0,5),(2,0,217,0,5),(8,0,211,0,5)]) (.leaf [(16,0,203,0,5),(64,0,155,0,5),(128,0,91,0,5)])) (.fork 3 (.leaf [(3,0,216,0,4),(9,0,210,0,4),(18,0,201,0,4)]) (.leaf [(80,0,139,0,4),(136,0,83,0,4),(192,0,27,0,4)])))
def levels219 : Nat → Packing
  | 6 => layer219r6
  | 7 => layer219r7
  | _ => emptyPacking
def index219 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 5 22 2 8 4 0 keys219k7
  | _ => fun _ => none
def g219 : Forest := ⟨219,7,fun j => samples219[j]?.getD (0,0),cols219,#[[]],levels219,index219,noFactory,noFactorySound 219⟩
def packed95r7 (i : Nat) : Nat := 0x7f
def layer95r7 : Packing := (1,0,0,63,0,0,1,packed95r7)
def samples95 : Array (Bits × Bits) := #[(0xc00720326701ffffff,0xd201291023501494a9),(0x110064c03d99ff40407f,0x1120e4d0a48887626246),(0xffffffffffffffffffffffffffffffffffffffffffffe20078ffce1e01807f80,0xffffffffffffffffffffffffffffffffffffffffffffe204a842ce1c258a4b14),(0xfffffffffffffffffffffffffffffffffffffffffffffc007f000fe001ff8000,0xfffffffffffffffffffffffffffffffffffffffffffffc24fe128fc0a5eb2a54),(0xffffffffffffffffffffffffffffffffffffffffffffffff80000ffffe000000,0xffffffffffffffffffffffffffffffffffffffffffffe64700030b77380c0c18),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000,0x19b857bc3000c0303060),(0x0,0x0),(0x0,0x0)]
def cols95 : IndexTree ColumnInfo := (.leaf [(8,0,87,0,7)])
def levels95 : Nat → Packing
  | 7 => layer95r7
  | _ => emptyPacking
def index95 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g95 : Forest := ⟨95,7,fun j => samples95[j]?.getD (0,0),cols95,#[[]],levels95,index95,noFactory,noFactorySound 95⟩
def packed127r8 (i : Nat) : Nat := 0xff
def layer127r8 : Packing := (1,0,0,63,0,0,1,packed127r8)
def samples127 : Array (Bits × Bits) := #[(0x303900c003900d6e2670026700fffffff,0x301900d10094442602348023480924949),(0xc1d10032600e93d99ffd99ffa0100ff,0x405108726228004882348823a492426),(0xffffffffffffffffffffffffffffffe430e22003c7ff31ce1e00e1e00c01ff00,0xffffffffffffffffffffffffffffffe410222025420b318e1c12e1c12c291614),(0xfffffffffffffffffffffffffffffff83f03c003f8003e0fe000fe000ffe0000,0xfffffffffffffffffffffffffffffff83e03c2a7f0aa3c0fc0b2fc0b2f6cb4b4),(0xffffffffffffffffffffffffffffffffc003fffc00003ff00000fffff0000000,0xffffffffffffffffffffffffffffffed40026438000c3ff00018b771c0301818),(0xfffffffffffffffffffffffffffffffffffc000000003fffffff000000000000,0xfffffffffffffffffffffffffffffffffbf8033000cc3ffb77dc000d81b0d8d8),(0xffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000,0x12afdd9bc2bdf0c00000e0000e01c0e0e0),(0x0,0x0),(0x0,0x0)]
def cols127 : IndexTree ColumnInfo := (.leaf [(8,0,119,0,8)])
def levels127 : Nat → Packing
  | 8 => layer127r8
  | _ => emptyPacking
def index127 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => samples127[j]?.getD (0,0),cols127,#[[]],levels127,index127,noFactory,noFactorySound 127⟩
def packed223r6 (i : Nat) : Nat := 0xc23db2443cab0045e65e8854050
def layer223r6 : Packing := (2,4,5,63,0,3,1,packed223r6)
def keys223k7 (i : Nat) : Nat := 0x2c80
def packed223r7 (i : Nat) : Nat := 0xc101049990201928c2040404126a3080021708200001060620580164058811801085c042a306801a4046010d0400217002a2c008381c3045c10106002040010e04380420d04340420106005041410000000000000000000000008200000000000008506141000000000000000000037cdbb60d2b44cbb20c4afcbdaf0b6ad4b3ac0aeaaca7a90a0a6c95a488ea2c87a1082a047b9d8729bc6b9a06698c5f9705694c4d92848914419003e8f43b8e8388dc358d0328c42f8b82c8ac298a026894238882087c1d8701a85c138481083c0d8300a824078180480c018009fd829dd53ded7550932fad5450932fcd53509329fd829dd51fd55354531ded7558921eed6558921fe562545219fd829dd609fc8754560eed62485609fd829dd50ded829dd50bed829dd50dee771c950ded761c950ded741c950ded731c950f6d531c950f6d6254950f6d5250950dec725c550f6c7254550fe87258150f795258150f7951581509fd829dd409fc8754d40fad424c940ebd6458140f795354140fe88254140f795254140fcd424c9309fe885d520ded744c920ded7648520f795354120fe93254120f795154120fe92154120fe562485109fc8795600a7d861c255b3d841c255e3e66956448fd869dd53f1e5591233e6e6695622eae6691222f2e5591222f4e558ce22f8e448ce229bd849dd51e766695611f56558ce11ee66688a11f665588a11fc63388a119dd839dd609ed829dd509ec8788950b7a8854050e7a6654050f3a4454050f5a3354050f688254050d797254050f6a2254050f7211540509f5819dd40bd9831d600bf1811d600e7a6695600eba6691200f3a5591200f5a558ce00f9a448ce00eea6688a00f6a5588a00faa4488a00fca3388a00ef26684600f725584600fd23384600fe22284600
def layer223r7 : Packing := (87,3,5,63,0,10,1,packed223r7)
def keys223k8 (i : Nat) : Nat := 0x627751b3c4a8399168bb851cca4c74682736b2c7145ec0ca562800ec0f31a6794e1ca17ff0540ac2701cd755000a6eee800000001ebda340e48fc1414e23a97821d2055127f0203843b120038a011000003d6918ea5a199299b190266d9e92000000001c40004fb9e4ceb212c44fb54d70002012303060cb9a5492a174dcd5218457359dcd6b5805e6e033440030020804007000813401c0180101191282
def packed223r8 (i : Nat) : Nat := (if i < 1 then 0x4583fea92c1ff50960ffaa2b07fd21583ff3baa1ff5d950ffacaa87fd74543feb22a1ff55150ffae6a87fd53543fea1aa1ff5c950ffac4a87fd52543fea12a1ff4c950ffae2a87fd61543fea8aa1ff4c550ffa42a87fd60543feb2a81ff54d40ffac4a07fd52503fe99281ff58140ffaa0a07fe554c3feaa261ff54930ffa84987fd514c3fe90a61ff54130ffa80987fd76483febaa41ff59520ffcaa907fd74483feb2241ff55120ffae6907fd53483fea1a41ff5c520ffac2907fd51483fe98a41ff58120ffaa0907fd40483fe98241ff59510ffcaa887fd53443feb1221ff54910ffa64887fd60443fea8221ff4c110ffa40887fd65803ff2ac01ff59200ffaa9007fd62803fea9401ff50a00bfceeb2f7c709577f334abdf59655bfceeb26fd65593bf2aac97f9dd54bfaecaa6fe66553bf2aaa9ef59154f7acb227be55912ff3baa7df95553f7c88a9dfe7750efebaa87df95543fbaa6a1fde558cfeeaa4677f9dd62dfacab177e5558bdf222c57f9dd52bfaeca96fe6654bbf2aaa5ef91152fbc66a97ed6254aff3ba857f5d942dfccca15fd7550bbf2aa85ef55142fbc66a17ed5250aff3ba657f5d532efcaa995fd744cbdf22265f754d32fda84997ed6588bf72ac45fb59222fdaa9117ed5388bf6a1c457f9dd61efcaab0fee22586ff3baa37f5d951dfccca8f7e55547ef19aa3fb88951feac2a8dfe774c6febaa63df95531fbaa698fee224c7faa8a637f9dd21bfaec90efe66486febaa43df95521bfae690fde33487f6b1243fd54521feacb08ff655847faa9c23fd58a11feaa508ff532846ff3bac1df95560dfac8b07be445837eb12c1fb88960dfac2b07f611582ff3baa17f5d950dfccca877e55543df222a1df54d50fbc66a87ec72543bea92a1fb88950efaa2a87f611543fcb02a17f5d850dfccc285fd74143df220a17f5cc50fbc66285fd72143f7110a17f5c450fec22285fe77502febb281bf99940bfaeaa077e55503deb2281ef50d40fbc66a07bd42503f711281fe54140bfcee985fd754c3bf2aa617f5d130f7c88987dd324c3f711261f74c530fec22985fe77482febb241bf99920bfaea9077e55482feba241ef91120bfae6907de33483f699241fb48520fec22907f950482ff3ba217f5d910dfccc885fd75443bf2aa217f5cd10fbc66885fd72443f711221fd4c510fea42887f875803fcb2c01fe95600ff2c9007f954803fca9c01fe50e00ff2c5007f952803fca1401fe4ca00ff2c3007f951803fc98c01fe48600dfccd0077e55803df22401f78ce00fdc45007f611803fcb0401fe54200ff281007f930803fc90401fe44200cfccd2aebe669139f2ac89d795633f3c8919eee6688bb72ac45eb91222f9c67116f666847bb2ac23f58ce11fcc4508f79501437d33401de95600f7489007da33803f511401fc84600 else (if i < 2 then 0x870098d0c0848e344800c0103a3800c20e363804468630305060848d001080a38d920022830582a238d1e0029a2a88f2410e363480c005240090830014208b1320c49090048c4188e12009088311c2401080060384802182c5090c1420304050560c001503058282282802828220a3944705045931e2c08651c342a191042146a78e0a08831851183020140c15042101014e2c541083020140a1504204c171c3484c82108080a7122a08460a8e5e4020a3971202008202031c58b01004903978c3822e1c0401210e5e3808020c5e3c618181012090c0c0019028584086032000a16102147084324204505103538b0810c10182004060601418910023058a121018201420042024e5e440086080c00a15003187288e30d4f1a004c170d0640c101018e3c60c06382122c004202031c48b0010c10181122c004304060848b001121438e502851a1d0c8161480c0051828c149002440a106002841420a00518009002801400a005002801400a005140090c00a0200a003001000a8854478a3c3221909e2510c04112785442a23c51e1511e28f08585443010449e1510c041127877e1bdcde46f0b75dba8dca6e036e7b5fda5ecfb671b24d816bbb5b5ac6d596a5f4eba61d2368cb43da0acfb676f373997cbe654f26391dc84e3d71c38b8c5262430eb853c2360cb04b811bfedfa6f8f7acbc1ddbeea9732b84dbbad996aab47d9d2cc164cb1c5876bf75e7ae9d6feb655acacc5612aef563aa7d526a4f513a86d3e69af4c3a57d28a91d47aa33514a861415a00cfb67b33c59d8ce7671337c9b44d5268132c98c4ba25b72ce960ca9a4fb270920485e4151fd8ea471e3751988c245c22ab12c88fc4121ef0ea867c2b6141093831c0ea05b020809c019fd6fbb7c23ddde9cf4178fbc49deeedc75d3ab5cfae7072ab8cdc4ce1970637fdbd6dde6e1b6d9b52d876af3529a6cd2268733cd9b0cb6654b239902c66625b06d81cbec5efaea1736b795af2d45688b30591ac59612ae7569aae1548a8953aa96948c9f34e526d934498e4b9a57d26c914483a3b11b08bd44a221d0bc851414206cfd67de3da9ea0f0c7643a81c9ce266f836e9b24d5c69a33f993cc4c6192f8178cb825b42c595f8a9c52c28f93849a84b225291f08de45421c90b08143da1d88e906f636e1a28ce061e30216c8adc55429d1480a0c4ec26212a892047622e11088504001f30f307643981bf0d906943301840b8057029e14209a84a022810707d03981b20c505c02ac12e08a03b01a40b804f01d80b804200d0007fd65553feaa2a7ff55162ffaeca97fd6554bfeba2a5ff59152ffaa8a97fd7354bfea9aa5ff50d52ffae2a97fd7054bfeb2a85ff54d42ffcaa997fd544cbfea92c3ff59551ffaa6a8ffd62547fea92a3ff4c951ffcaa98ffd524c7feb2a43ff95521ffaa690ffd5 else 0xbc30a24208d0b0803104200c9708bc10920292084585048c100a8c08a86482a428982145223224287002490e046703431324380143282430c4c2262421246222982484450668242302190908c4908a8c0c22384006ca442c2192060b12243141481214111d0d04c17160a30922189241441972d0470884138622420952f1141d1234311b31046888e0a00c985823868a446c48a0a40cf03805c4480c1401d2c0382c3320e01790a05802e445021c6860430c9060890a0890a0890a0319246006884450486104821048810080c083100900240584405840104808748405040101211046006c8406848a085041410421d0421e2421e1821e9010e107890318f1210f12122801218010d8010d8011e0a1058429d08d0508e450829908ac508283020241e18342801800c33a5c318184178e2c304284040639a18282020058b0c14008b0c1cc2815203001162640e922200a2200a1161c185020240a161022018e0e0028c18270c0618c088324106082142030400c8c1418200305400a0050028018a6144618284051ca8c3030582a23971e08214202002c5820862e1e0c90414a5e3c704a0e0c180903a48208b0c1420014341060881d1a68b213c8901800a30518292004881806c6870018008c151c6c8141018e245860028600286002860020e106))
def layer223r8 : Packing := (311,2,5,63,0,13,1,packed223r8)
def keys223k9 (i : Nat) : Nat := 0xc38699a008002496000000000140dc4585a000005e517d9a0001d63edc000318c001c69e6f3809981e4400064ad540446569aa874d84209633c3e1f6cfc482d9c5e3e48629414b809ac43874ac0ba23e1591528e7da26b25660a9b5136caf08c1465e9d0403322055dee68d7061424cbc72e4e64b0c4ca7413163dc6530d8e45224000127e5576ae8852314529f928de369785e827714788ed6b3877a1884c2297ad6c250e8f808a4400086bf9980d800e22da4aa36e5cdae2376a97b99760345dc4700c181698934420e6c2e17f1b94215e83d0412a593f6f2e1ae16ee49b1635c638d016e237985390001654d90f20254a10051d895d18f024f81bc78cbb8cf0002ab247dd19e0f441cc69d3501d104d96dcdd64d817ecd527006750df247cabf875340001e8b93ddaf080941479519d6dd988235cc9060fac55a79fa680000648368003d55c25a0ff3480002c20001c558ec000e8982a0001aafa2d0000000cf600013e8001c0582cb9fc000000213800000044700033f612623fe4f4030d1e00087cb8a3e5e056664f49de3600092449251d4c8c21e2418a41892000283c5280000000000470b0844b79bb8f467725203ffd30000d3ca18766cc87896837c060000d3c6901a3bce1378199dd10ed9b56ab6b9a8ceec2c5c24991009c0bcc62c30e310003cc919b810f068bd5188e8dc910ac017e0d521593e214f8b781160c800092640559bfe172e7f59908658290d00d20cc0012190006c9505907c000386c97c84271efb0d23404eb070000263cc5e75fa880000004005170000c84c6ba13c0018850500160101031802570e01110010111900020009000306010300050d01a5065076070809010000000c1d00000001031008000f060c010d0d2a1600010100010002000723081d080a1a13090e0500024a1b3b00000200120a06030007051e0b20100e0700040219
def packed223r9 (i : Nat) : Nat := 0xb098f4e44c2b10af44e34ee8c2c2b903ce2c25b540f30c2c274e44c30abc27103cee0c2b00ce44e2d00ceccaa8c2ae0d03cea0c29c0ce44e30ac426903ce30b09b40f32630b09a40f3a230a68340f38c2c2c4e44c08c2c344f330742b9b44e30b48c2c2bd03cc34252539130d4033a128d0927d03cc31d09b44e2cf0ce4460423513cb0d03c70ce44744e0c70d03c60422d13cb1d2224147d4f01c8360678c316e2ac504949111f839c648b413e2343c0600a81081b02a03c048003fd65ff957fd64ff553fd53ff50ffd62ff54bfd42ff4cbfd61ff547fd31ff487fd60ff543fc50ff503fd30ff483fd10ff802fe66df957be44f78cfee22fd847fa00
def layer223r9 : Packing := (29,1,5,63,0,11,1,packed223r9)
def keys223k10 (i : Nat) : Nat := 0x1892e0a075aa58000019000000000000021c00006180117000000000f5310000010802a400002a4000000003f796000011a0037cd36a0046000000000003a0000000000310000000000000001a000000000003ecf3800e40400420
def packed223r10 (i : Nat) : Nat := 0xa0f1ff
def layer223r10 : Packing := (1,0,5,63,0,0,1,packed223r10)
def samples223 : Array (Bits × Bits) := #[(0x2030010e01007c0c001c803267007fffffff,0x203441060144140d2004a410234804892291),(0xac00033e6004d100193003d99ffd00401ff,0xac28810e6294910c39318a48831d324c866),(0xffffffffffffffffffffffffffffc300063c7800722001e3ffce1e006007fe00,0xffffffffffffffffffffffffffffc30a1e3878a362228aa151ce1ca56a669d4c),(0xc0007c07fff83c001fc000fe0007ff80000,0xc009a402a0b83c04bf8098fc0157170582c),(0xfffffffffffffffffffffffffffff00007ff800003fffe00000fffff80000000,0xfffffffffffffffffffffffffffff00c17ef00c202670c00610b77c60c431188),(0x0,0x0),(0xfffffffffffffffffffffffffffffffff800000003fffffffff0000000000000,0xc50e000000c0198715e8e30001801806030),(0xfffffffffffffffffffffffffffffffffffffffffc0000000000000000000000,0xfffffffffffffffffffffffffffff3af05bfd5f07c038000700000e00e0381c0),(0x0,0x0)]
def cols223 : IndexTree ColumnInfo := (.fork 15 (.fork 7 (.fork 3 (.leaf [(2,0,221,0,8),(4,0,219,0,8),(8,0,215,0,8)]) (.leaf [(16,0,207,0,8),(128,0,95,0,8),(1,0,222,0,7),(64,0,159,0,7)])) (.fork 4 (.leaf [(18,0,205,0,7),(136,0,87,0,7),(0,2,204,17,6),(0,8,86,129,6)]) (.leaf [(0,16,141,66,6),(0,128,23,72,6),(1,2,204,16,5),(1,8,86,128,5)]))) (.fork 8 (.fork 4 (.leaf [(3,0,220,0,5),(5,0,218,0,5),(6,0,217,0,5),(9,0,214,0,5)]) (.leaf [(10,0,213,0,5),(12,0,211,0,5),(20,0,203,0,5),(24,0,199,0,5)])) (.fork 4 (.leaf [(64,16,141,2,5),(64,128,23,8,5),(68,0,155,0,5),(80,0,143,0,5)]) (.leaf [(130,0,93,0,5),(132,0,91,0,5),(144,0,79,0,5),(192,0,31,0,5)]))))
def levels223 : Nat → Packing
  | 6 => layer223r6
  | 7 => layer223r7
  | 8 => layer223r8
  | 9 => layer223r9
  | 10 => layer223r10
  | _ => emptyPacking
def index223 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 3 0 5 1 0 keys223k7
  | 8 => lookupWord 29 99 6 11 7 0 keys223k8
  | 9 => lookupWord 103 358 8 13 9 0 keys223k9
  | 10 => lookupWord 9 79 3 9 5 0 keys223k10
  | _ => fun _ => none
def g223 : Forest := ⟨223,10,fun j => samples223[j]?.getD (0,0),cols223,#[[]],levels223,index223,noFactory,noFactorySound 223⟩
def packed255r7 (i : Nat) : Nat := 0x1c9bdb1a5998d8175695d5145392d211508fcf0e4d8ccc0b4a89c9084786c6054483c3024180c014d76d68864c865c699edad10ca100b8d39db32199420171a75b694432443ac34cf6d288654805869b6d910eca900b0d35db3a219521970a79b674432440ae14db6d486648815c29d6d9510ca10eb053cdb2a219320560a73b6843b2640ac18cf695a4660760431aed2b46cc0ec08639da468d981d810c6db4ad13303b0218eb691a2660760431e6d1b44cc0ec086175a8696995c471a1eb714ccccb88e38ad6a1a4a656118687adc5333bac230c4f5b9aa9761da11c3b350d1d32b80e143e6e299999701c3478d42c230ae03851f1b8a66115c070c9e152b8ac2b82c163c2e17158570583174d43454cac03050f9b8a667758060d1e350b88e2b00c14bc6e299845601828f8dc5333ba200868f1a85d87644010a5e3714cccc8802113e6e6aa5d8768022f8dcd54b88e30046f1b9aa96118600
def layer255r7 : Packing := (39,5,5,63,0,8,1,packed255r7)
def keys255k8 (i : Nat) : Nat := 0x2970f0c4aa2a7e6a81221bf7240a6ed846661fc3347b0db94833200001a380040935891360062ed2801e4c1c6b0000011400690006b15300068940eaf067000112809308c01
def packed255r8 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x8484470ead9998484470c7e6a2995c070d7668e995c070a7e6a2995c070b7668e995c070d3e658965c070d3ea66665c070d7c644915c070a7e6a0615c070b7668c615c070f3c584615c070d7ca66115c070f3c99a115c0708f768e9961d608fb68a9961d60a7b68a889dd60abd2a17158560af968a8884560a7e2a1715c1609be2a5615c160f3c5c5615c160c5fa667761460cdb615921c460c7d661711c460e5d615711c460addaa98584460e5d9dd8584460cbe6a29958060dba68a9958060abe6a29958060bba68a9958060d3e65c9758060d3ea667758060dbc6449158060abe6a07158060bba6887158060f3c5c47158060dbca661158060f3c9de11580608df6969961d108f768e9961d108ef69299619108fb68a9961910c3f6589661c10a5f6949661c10a6f6909661c10a7768c9661c10a7b6889661c10c3f65c9761810a9f6949761810aaf6909761810ab768c9761810abb6889761810c3fa667761810a3f6a1761d810c3f661761d810c5f61d951d810c9f619951d810c6f61d941d810caf619941d810c7761d931d810cb7619931d810c7b61d921d810cbb619921d810c7d61d911d810cbd619911d810c7e61d901d810cbe619901d810a3faa987998108df6a47661410e1f5d87661410acf6907661410ad768c7661410adb6887661410add6847661410ade6807661410e1f9de66614108ef6a47661010e2f5d87661010acf6947661010ae768c7661010aeb6887661010aed6847661010aee6807661010e2f9de66610108f76a47660c10e375d87660c10ad76947660c10ae76907660c10af36887660c10af56847660c10af66807660c10e379de6660c108fb6a47660810e3b5d87660810adb6947660810aeb6907660810af368c7660810af96847660810afa6807660810e3b9de6660810cfc6a29944010afc6a29944010d7c65c9744010d7ca667744010dbc65896440109fc6a47644010afc6a07644010f3c5d87644010bdc6947644010bec6907644010bf468c7644010bf86887644010dbca666644010f3c9de66440109faaa99221e00b7668c989de00b7668c919de009f6aa99321a00d769dd9321a00b3eaa9761da009fcaa9911da00bba6889899a00bba6888799a00bba6889199a009de696995c6009faaa9921c600dba999921c600b7caa9711c600f3c999711c6009ee69299586009f6aa99318600d769dd9318600bbcaa96118600f3c9dd6118600bec6909784600bf86888784600bdc6949684600bf468c8684600f3c5d87684600bdc6947684600bec6907684600bf468c7684600bf86887684600f3c9de6684600a7768c989de008f768c989de00abb6889899a008fb6889899a009f668e995c2009fa68a995820083f6a2995d87687d6a2995c4718bd6a2995846187e6a2995c0708be6a299580608fc6a29944010 else 0xcf7a219318570d7769d9318570df66819318570af768e8884570af768c9161870af768c96604708ff6a299584709ef6929958470aef2a58458470cefa658458470eaf6998458470eed68584584708ffaa99818470cfb29d92a2160cfb28592a2160cfb65d92a2160cfb64991a2160afb68a8821d60cefa219421d60dee6819421d60afb68a889dd60aef6908760560afb68a88205608ff6a48720560aef6908720560cf7a219320560cf761d9320560cf721d9320560db769993205609df696995c5608ffaa8985c560afb68a885c5608ff6a6881c560afb68a881c5609fb2a1921c560cfba21921c560dbb699921c560dfa681921c560bbb6889758560bbe6809758560baf6908758560bbd6848758560afb68a8884560bbe698915c160bfa688915c160b7e69c815c160bf668c815c160f3e5c5615c160fbc5c5615c160f7c5c5615c160f3d5c5615c160afb6889161c60afb68897604608ff6a2995c4609df696995c460adf2a5855c460cdfa65855c460e5f69d855c460edd685855c4608ffaa9981c4608ff6a487219108ffaa8985d9108ff6a6881d910cdfa21951d910cefa21941d910cf7a21931d910cfba21921d910a7f69a9961c10adf6949661c10aef6909661c10af768c9661c10afb6889661c10abf69e9961810abf2a67761810adf6949761810aef6909761810af768c9761810afb68897618108ff6a2995d8108ffaa9981d810cdf695981d810cef691981d810cf768d981d810cfb689981d810c7f2a58799810adfaa97661410aefaa97661010af7aa97660c10afbaa97660810cfd2a1911da009df696995c6009ef6929958600977aa9932067795faa99520277c3f6a2995d876a3f6a2995d876d3d644915d876d3e640905d876add6949060476aed6909060476af568c9060476af96889060476cfc6409060476ade6949160076aee6909160076af668c9160076afa6889160076cfc6449160076b3768c919de66b1f694909de669bbaa99220666d3b9dd92206669afaa99420266d2f9dd9420266a9f6968899971cbba666660871c7d6a2995c471d5d696995c471a7d6a2995c471b5d696995c471d3d658965c471d3da66665c471d7c640905c4718df6969961d618ef6929961d61a6f692889dd61c77a667760c61cbd6a29958461dad6929958461abd6a29958461bad6929958461d3d65c9758461d3da667758461dbc64090584619edaa99421e11b5d694989de11b5d694909de119ddaa99521a11d5d9dd9521a11b3daa9761da119fcaa9901da11bad6909899a11bad6908799a11bad6909099a11a5f694989de118df694989de11aaf6909899a118ef6909899a119dd696995c6119ed6929958611ab768e8899970c7d2617158570af568e8884570cafa666661070ce76119318470cbd6616118470ead6116118470aedaa9) else (if i < 3 then 0xd9bd83d7dd77d56d3ed2fd20d1ad02cf3cdbcd5cb4caeca8ca2c9cc96c90c8ac7bc75c5dc57c3fc30c2ac1bc15bfdbe5bd6bb5bafb8eb88b79b73b64b55b46b40b31b22b13b0db07b01af2ae3addaceabfab0aaaaa4a9ea98a92a83a7da65a5fa47a38a32a23a1da059f69de9cf9c99ba9ab99c99698797896994894292191b91590f8ee8e88c78c18bb8b58af8a98a389488587f87086185284c84684083a83482e82882281c81681080a8047fe7f87f27ec7e67e07da7b079878076875074a74473e73873272c72672071a71470e7087026fc6f66f06ea6e46de6d86d26cc6c66c06ba6b46ae6a86a269c68d68768167b66c66666065a65464e64863963362d62761861260c6066005fa5f45ee5e85e25dc5d65d05ca5c45b55af5a059a58b57c56d56755855254c54654053a53452e52851951350d5075014fb4f54ef4e94e34dd4d74c84c24b34ad4a747d47747146b46545f45945344d43e43843242c42642041a41440e4084023fc3f63f03ea3e43de3d83d23cc3c63c03ba3b43ae3a83a239c39639038a38437e37837236c36636035a35434e34834233c33633032a32431e31831230c3063002fa2f42ee2e82e22dc2d62d02ca2c42be2b82b22ac2a62a029a29428e28828227c27627026a26425e25825224c24624023a23422e22822221c21621020a2041f51ef1e91e31dd1ce1c81c21bc1b61b01aa1a419e19819218c18618017a16b1651561501411320ff0cc099066033000afd6829960476adf6949060476aef6909060476af768c9060476afb6889060476afe6869960076adf6949160076aef6909160076af768c9160076afb6889160076cdf29995a2171cdf28195a2171cdf65995a2171cdf65590a2171adf6968821971cf7a219321971df56859321971adf6968899971af768c8660171adf6968820171af768c8620171cefa219420171d6f69d9420171cef6199420171cef2199420171adf6949061871adf6949660071cef29d94a2161cef28194a2161cef65d94a2161cef65190a2161aef6928821d61cfba219221d61df96859221d61aef692889dd61bbd698905c561bed690905c561afb6888760161aef6928820161afb6888720161cdfa219520161cdf61d9520161cdf21d9520161d9f6999520161d7d65d7120161ddd6557120161aef6909061c61aef6909760061cfe2a1901da11cf729993a2170cf728593a2170cf765993a2170cf764d91a2170af768e8821970cdfa219521970dde6819521970af768e8899970adf6948660570af768e88205708ff6a48620570adf6948620570cfba219220570d7b69d9220570cfb6199220570cfb2199220570b7768c965c570b7e680965c570b5f694865c570b7d684865c5709ef69299585708ffaa89858570af768e88585708ff6a68818570af768e88185709f72a1931857 else 0x30f0c00eb084068d4216161c2c3002ac4138cc4131e1000000000c3430032c0100016b0fe30f44a00b0b0e16180c6e2098d082ec61003ba37883000000000030f0c00fb184028f421612103090c008b004e13004c784b985f18600f709e10c0e082068810982130400982c4058e08000014042808014054a0a981000000030d0c00db104028b401612103090c0617004c68413610b80081a304240848100240b10163025ec2f883007f84f00600001630fe10c01ce1bc0180000000005410a82005415282a7040000000000000000000000000000000602008004935122935122935122935122000000000000000000000000000000000000000000000d002041078c1000800000d00204107881000800000000020000000f0020780103800f001d00306801000800000820f0820010010010400000280181400c1078fc5e1f048001000001041e0040020020020800000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000020000820000000800000000020000000e002001001c004002000000000000000003c0080e0040e002c0040de3f1787c12817c7e2f0f82502f8fc5e1f04a04f1f8bc3e09409e3f1787c12813c7e2f0f825ed0ecaec4ebeeb8eb2eacea6ea0e9ae94e8ee88e82e73e6de55e4fe37e28e19e13dfbde3dd4dcedc8dc2dbcdb6db0da1))
def layer255r8 : Packing := (390,4,5,63,0,12,1,packed255r8)
def keys255k9 (i : Nat) : Nat := 0x10830000000001d778a180005966c8330ccfa09b10715d000000103b753021853028a960a2f455c8ed5affcb40018bc0002264169a9ed918a382d6000a30496c00000087aecac001b767464b0000016e000287c00132164a01c930800076f612be1eb3f40c434ac392cebbd6c609674d878131ace2f2dbe90789a0d46f1d38602713f93ca88732a663d668be63d18ed87708dc009eff28195582d811645117f051bce60d9e3a8001527f69520d89e0feca867120335d2cb1a52c0fbe60c0151053a099bc0691a0000009605c280002cd2eacbae095f01c9673157903b060006596ce91af92ffa5fe022a54e1a792150a9bc88885c0695200000ad58b4001ec77388064ac9ca300030584e9b1622ce3e4001b6a70548540003119191d1c000ae3f822d840000d6267c3deb0473da8d39964bd2824a9a927638cc559631a04dab41b1588780011132818001d24817000238000054f5949574001e8f7829d0bc9144f49abdf82ad4c61b79395c8f81142fbc78816d3bc2c6b0d24ce461a53ae697cd25a1ed88edb4e4cc327b55a648562a2f9bec61f51842cdc9a19236d3f04cc2b095400040f0001d63756ce05e88c893890001961622b068002ec1e1b13c70e9ae110ea7e6d94ca69222ba518b9008d10007d38000128a338e14cdd42c98eb10c58800002e1aff04becc7b67a5dd53b080003b7d2da97bb7c4451dbb91f95c0001dedd5e45200000f4ce70002b916700008a49a1da80000f3d8003ef1a9585114ddc9cf75c14ec378214b76b8d0cd5e145200000036c4eef63322136ae3502737454955106d10cbf580fc7932ee8bcdff80f980b12e48b1273a608500014d00046282d2d95bd764b4c176736e7da15703ae44000442ac5c00015acde5e49aafc1bcc6713b568a09dd231f54ee000104a94f0a1f48a80eda9624baaa3ab4842c231ab8e74fbd591145a6e13552ad84b9f313863f5189b27e68c630005401a5c0ebb79bdce1b968d01c79b340077d82d74e4101124450b203431b080c014000008f00182000004b1b02002020001001060c08d12301101810001046c081043c70d0008183020820108ec3800010a80365a0081200581081010a10040020e141870600305161808a3c08487000928602040430a0808b000820202000861a7000a02d2295
def packed255r9 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0xebb0ec085df65476042f7b283b0217dd931d810bf6c90ec085fd64476042ff3203b021afd8799810e7f3bccc0867f61e660435fb0d33021b7e7761410dbebb30a086df1d9850436fcccc2821bbe7761010ddebb308086ef1d98404377cccc2021bde7760c10deebb306086f71d9830437bcccc1821bee7760810df6bb304086fb1d9820437dcccc1021ff29944010ff8cba20087fc25d10043fe4ee88021ff19644010ff84b220087fc5d910043fe0ec88021ff26644010bfccb10f005fe64487803bf1313bc01df8969de00efc48cef005fe65c86803bf4ee434017f99121a00bfd4caed005fe26176803bf4eebb4017f9911da00f7c4c4cd007be25e66803df10f33401efa7799a00f7c48ccd0077e9de66803df2ed334017f99720600efd3b903005fe65881803df4cc40c017fa995c600bfc4c2e30077e21d71803bf4eeb8c01efa665c600bfccb0e3007be99871802ff532b0c017f89858600bfccbac30077e9dd61803df10cb0c01efa6658600ff8b8ac3005fe65c61803bf4ee30c01ff09884600ff84bc23007fc21e11803fe4ef08c01ff09684600ff843423007fc5da11803fe0ed08c01ff26684600efd3bc23007be99a11803fe2e308c01ff16184600cfe4c4ef004ff262778027f930bb401cfd761da00bbeca8ed005ef65076802fbb263b4017ed921da00bfac88ed005fe640768035f93133401cfe7799a009fe4c4cd004ff26171802fdb2438c01df5711c600bfcc80e3004ff26161802fbb2630c01ef56118600bfcc80c3006fd26211803becef08c01ef666846009fe4c423005fea6570803bf4eeb8401efa665c200efcb8ae1007fc84570802ff532b04017f99758200efd3bac1007be99960803df2c2b0401ff21158200bfd4ca21005fe65d10803bf4ee884017f99644200f7d33221007fc84510802bbb2640cef57d9520277a7f4caec3b4fda65811da7f532c00ed6ed9220666b5eca101334df656885c67dd32c10e3aee6660871afb4cae238f3d999711c677b29442c33de9960c61cef3bb0630dbda65611879eceeb08c37b59421e11bbaca90d08f3d5d876846eeb2a3b4237b5941da11beac98ed08df964876846fe3203b423cf67799a119eec9d10b84efa65841c357cccc20e1bb58484470afd4cae03873e999701c3be422b80e13ed92a21609bf4cb0a3065f9dd851836eb0b088c16fa9958060e7d3bac0307bc845601823fd32c38212fe9961810c7f3bb0c0863f61e660432fceec2821a7e6661410cdf3bb08086af999840433bceec1821ade6660c10cf73bb04086bb99982042fe53288021df27744010f7933220085fa64887802fb32643401cf9761da00bbcca8ed005ee65076802fb3263b4017e9921da00bf8c88ed0073e9de66802fd32438c01df1711c600becc98c3007bc58461803be4ef08c01ef26684600 else 0xa8ed08def65076846fbb263b4237ed921da11bfac88ed08dfe640768475f93133423cfe7799a119fe4c4cd08dfda6571847beceeb8c23ef6665c611bfb4cac308dfd65d61847beceeb0c23ef666586119fecb510b86f764e885c27fb23442e17dd93a2170d7ec310cb85df654865c35f931332e1afe8899970e7f3bcccb87be242665c27f931332e17ed9220570dfac0902b857fa65715c33fd10b8ae1cfe665c570efa40ae2b877e241715c27f930b0ae1df571585709fecc0c2b857f65c615c2fbb2630ae1ef56118570bfcc80c2b86fd262115c37ed1108ae1df49784570efb3bc22b87bd99a115c27f93108ae1df571845709ff4cb0c386bf61a661c377b2cc20e1bbe6661070ddec8b08384ffa65811c35fcccc08e13fd9858470d7ec32c2386ef611611c37eb02b08e13fd9818470ddec20c2385f764c611c3deac2308e1bf58684470f7b33422386ef612111c37eb03088e1dfa995c070efccb2e03877e259701c3bf4ccb80e1df9915c070efc48ae03877e585701c3bf0c2b80e1dfa115c0709fecbd10b06fb64a885827fb23442c17ed92a21609ff4cb0eb067f61c87582f7b2843ac19fc989dd60cff444eeb077e242775827f9313bac19fd879dd60d7ec3cccb073f9de66582fbb2640ac1bf581205609fe4c2e2b04ff66071582dfb2c38ac17ed921c560efab88e2b05fe64071582dfd32b0ac1afe8858560e7f3bac2b07bd20561583deae2b0ac1ef89058560dfa4c422b06fda22115837eb0f08ac1df67784560f7a4b422b07bd99a115827f93108ac1ef56184560bfd4cae0b06fea2170583bf10eb82c1dfa775c160f7c4b2e0b07be99970583bf2e2b82c1ef9615c160ff908ae0b04ff661705827fd32c38c19fd879dc60dbecbb0a306df9dd851836fb22c28c13fe9960460cff3bb02304ff661711833fb0eb88c1b7d855c460dfac0ae2304ff660711836fb0a388c17ed921c460efab88e2306fd61e11183becef088c1b7d8584460dfac0c22307bea6560183df32eb00c1ef89758060f7d3bac0307be64560183df122b00c1ef97158060f7c38ac0307be845601827fb2f442213fd96a21109ff4cb0e8867f61c874433f9313ba219fe889dd109fe4c4ee8867f61e774427fd32c32219fe7761910d7ec310c884ff661764427f930bb2213fd981d910e7ebb0ec885df65476442f7b283b2217dd931d910bf6c90ec885fd64476442ff3203b221afc9899910d7f444cc886bf61e664439fcef332213fc9899910d7ec34cc886fd61e11443becef08a21bf58684510f7b33422884ff661704427fb30b02219fe9961c10cfecb30e0867f259870427fd32c38219fd879dc10d7f4cb0c086bf65d860435f92ec3021afe77618109ff4cb0c0867f9dd860427fb30bb0219fd875d810d7ec32ec084ff660760433fb0e3b021afd861d810e7) else (if i < 3 then 0x2b06ffa2081582ffb2e40ac1bfd8720560dfe43902b05ffa6571582ff930b8ac1bfc985c560dff442e2b06ffa2071583df92eb0ac1efc8758560f7f3bac2b07bf5c561583feae2b0ac17fc9884560dff44422b06ff61e11583ff2ecb82c1ff8915c160ffc40ae0b07fe5c570583ff2c2b82c1ffa115c160efeb8ae0b07bf585705837f922c38c1bfc9760460dff3bb02305ffa65711837fb0f088c1bfd97a2110dfecb510885ff65e88442ffb2d44221bfc9661d10dff4410e885ff65887442ff9313ba21bfe889dd10dfe4bb0c886ff9dd864437f90ec3221bfe8821910bfecb90c886ff61c864437f90e432217fe995d910bfe4c2ec886ff261764437fd10bb221bfe881d910bfe4c4cc886ffa22664437fb0f33221dfd715c110f7eb0ac0886ff259870437f92ec3021bfe7761810bff4caec086ff61e66042ffd32bb401bfc985da00bfec88ed005ffa65718037f930b8c017fd961c600bff4cac3006ff26161802ffb2eb0c01ff57158600bfecb8c30057f644869debfb20434ef5fd9620677afec81033bd7f658809debfb22404ef3fd91a21769fec8510bb6fd604815db7f300402edcfe995d876e7ec8aec3b73f245761db9fb20bb0edcfc905d876dfb4cb023b6fd641811db7e920c08ed3fe9960476dfd4cb003b6fe645801db7f122c00ed3fe9960076b7ec890f335bf6408799b9f9313bccdcfc919de66e7e484ef335bf65c8199b9fcee40ccd6fd9020666b7ecb9013373f9dc8099adfb22404cd9fc989de669fe4c4ef335bfa657699b9fceebb4cd3fd96a2171dbecad10b8cff642885c6efb2b442e3afd8621971beec990cb8ebf262665c75fd11332e3cfe7799971f7a48cccb8cff262665c6f7b28402e3bf980201719ff4cb0c38ebf61a661c77db2cc10e3bee6660871df6c830438f7da65711c7beb2cb88e3df4965c471efb332e238f7d641711c7be920b88e33fe9960071d7f3330038cff65e8858777b29442c33fd90a2161bdeca510b0cffa65875873fb0e43ac37ed9221d61cfe4c4eeb0e7fa2277587be9233bac33fc989dd61cfec3ceeb0ebf61e665879fcef332c37f6995c561dfb442e2b0f7d21d71587beceeb8ac3ef4965c561f7b332e2b0cff66171586efb2a402c3bf980201619ff4cb0e30e7f61e771877bb2ec18c3bde7760c61deec830630fbda6561187deb2eb08c3ef49758461f7b3bac230fbd64161187de920b08c33fe9960061cff3bb0030dfd65887846feb2043c23df4989de11efa4b4ef08f7d24277846feb2e43423df67721a11bfac810d08dfda6576846fe930bb423df6775da11bfac80ed08fbd26266847de92f33423ef48799a11f7b3bccd08fbd24266847becef33423ef57699a11bfacb90108f7d9dc80846feb2c40423ef66620211cfe4c4ef08cff262778467f930bb423cfd761da11bbec else 0x96252a8a4d9494291a5218a33945c28a25118a219438286a50a8a0793f427ca4f289d393a027024d889a1931c262a4bd896b92b8253249f892f9240247a48d89199214241a48188fd91f823ea47a88f391e423c247788db919822ea45c88b59164228a44d88899104220243a886390a8214a423883b9060209240988018ffc1fea3f987f18fc41f6a3e987d18f941f223dd87ad8f3c1e3a3bf876d8eb81d3239e872d8e3c1c3238486f98dd01b5a36486b98d541aa234d868d8d0019ca33186538ca0192a31d86298c34183a30085f18bc4175a2e485b98b54167a2c885818ae4159a2ac85498a90150a2a0853f8a7414e229b85358a6814c229685298a4c148a28f851b8a301452288850f8a18142228285018a0013f227d84f989e813c227584e789c8138226e84d989ac134a26884cd8994130a25f84bb897012c225684ab89501292250849f8938126224b84918920123a2468489890c120a238846188c0114222084318844104a20083fd87f80faa1ed83cb87940f1a1db83a7874c0e8a1cf839d87380e221c2837f86f80dda1b9836f86d00d921af835986ac0d4a1a5834986840d0219e833386540c7a188830385f40bc216e82d1858c0aea157829b85200a1213c826d84c8096a1278243847008b21108213841407da0f581df83a807220de81b1833c064a0c3817b82e005920ac814b827c04c209181178218040207a80e981bc034a06380bb8160029204d8091810c01ea037806380b0012a02080358054007a009800980006ff646885db7fb21442ed7fd91a2176bfec8510bb6ffa20815daffb2040aedbfc8160176dff44100bb5ff644805db7fb02402edbfc8120176dfe483023b6ff245801db7fb2d442e3bfd90a2171bfecb510b8dff642885c77fd10432e37fd9021971bfe4c4ccb8effa22665c77f90cc02e3bfe8820171bfecb100b8eff618805c77f90c402e3bfc9061871dfe4b30038eff999801c77fb2f442c3bfd90a2161bfecbd10b0dff642885877f920c3ac3bfe8821d61bfec810eb0dff262775877fd113bac3ff5765c561ffa482e2b0eff21d805877fd10402c37fd9720161dfec3900b0eff21c80587feae2402c3bfc9061c61dfe4bb0030eff9dd80186ffd32bb423bfc985da11bfec80ed08eff65a885c37fb23442e17fd96a2170bfec8d10b86ffa20865c2ffb22432e17fc9899970dff444ccb86ff219815c37fd1040ae17fd9620570dfec3102b86ff218815c3bf92cb8ae1dfc865c570eff332e2b85ffa65615c2ff930b0ae1bfc9858570dff442c2b877f5c5615c3feae2b0ae1bfe8818570bfe4c422b86ffa22115c37f922c30e1bfc9660470dff33302385ffa65611c37fb0d088e1bfd97a2160dfec8d10b05ff65e88582ffb23442c1bfc9161d60dff4410eb05ff64487582ff9313bac1bfe889dd60dfe43b)) else (if i < 6 then (if i < 5 then 0xe3e2e02e949f8f8b84b252726e3e2e1e09b8f8b8782421171013c7c4e3e2e0a61e138f878258784e3e1e0951d138f87825e3e2e0e184978f8b8213865e3e2e084e1948058404b1b138f8b8698684e2e1e0961a138b878254644e2e1e0978f8b8782125e3e2e184e0978f8b86138258584e3e2e1e09a16138f8b878268584e3e2e1e09915138f8b8782684e2e1e08b96138b87822e584e3e1e08a96138f87822a585e3e2e08996178f8b8226585e3e2e18896178f8b86225e3e2e1e084978f8b8782125e3e2e1e084949f8f8b86426e3e2e0938f8b87809a526e2e1e02f949f8f8780b6526e3e2e02e949f8f8b84b252726e3e2e1e09b8f8b878242725e3e2e1978b8780978e52625e3e2e0978f8780978a5e3e2e1e0938f8b87824a9d9537aa6454b2a939523aa3c5462a8a950faa18541aa8094fda9f453caa7594e3a9bc5362a6994cba98852faa5b94afa95852a2a50949da934524aa459485a8fc51e2a39946da8d4518aa2d9453a89c511aa1f9437a86850c2a149423a844506aa0b9413a81850129fe93f7a7e44fb29f293dda7b04f429e493c1a7744eca9d593a7a7484e729cb9391a71c4e229c1937fa6f84dd29b89369a6cc4d8a9ad9353a69c4d1a9a0933ba66c4cba9939321a6344c4a9859307a6084bf297c92f1a5d44b8a96e92d7a5a44b3296192bfa5704ac295592a5a53c4a62949928fa5184a129409279a4ec49ca9369267a4c4497292c9257a4a44932921923da47048d2917922ba44c4892911921da430485a9089207a40848028fd91f5a3dc47a28f091dba3b4474a8e691c7a38046ea8da91aba34846728cb9193a32046328c49185a2ec459a8b29163a2c445728ad9155a2a8450a8999123a22043fa87790dfa198431a86090bda17442da85990afa15842a285290a1a13c422a8439083a0e841a282c904ba09440f281c9035a06440ba80f9011a0203ff27fc8fe99fb43f2a7e38fc19f803efa7dc8fb79f483e827c68f819ee43d927a98f519e883d0279e8f399e543c8a78d8f179e243c327858f059e083bfa7788ee39dc43b427668ebd9d5c3a7a74d8e959d283a4a7468e8b9cf039d27388e6d9cd4399a7318e5f9cb8396272a8e519ca039327248e459c84390271e8e3b9c7438d27188e2d9c54389a70a8e059c0837d26f28dd59b8c36d26d28da19b40363a6c58d859b0435fa6bb8d739adc357a6a98d439a6c34d26938d239a40347268c8d0999f833ea67a8cef99d0339a6728cd3998c32da6538c97992c321a6418c7f98f831e263a8c6598c031326248c399854306a6038c0397e82f925ea8bc597702ea25cc8b9797282e4a5c18b7f96f82dda5ba8b7396dc2db25b58b6996d02d525a48b3996582c6a58c8b0b96102c125808af195d42b8a56f8ad195a02afa5578a9f95202a3a53f8a7994e829b25358a5d94b82 else 0x11e8110287600a19802018218201821c20704e2e3e0e19818138f8b878268760860c140c0b8780406110586e3e2e1e0842280106656261601b159c19958985806d9c767066261601b159c5c1c18178f8b87821096004181004000f884474605e0e2e1e3441c546f8119138b8670705e0e2e1e3441c978f8b8781126154644e2e1e0a59c489c978f8b8712782801829c1a8a86806e947a00782161608a0018982282080016061110e3e2e1e027241c0c08040098587171611e3e2e1e010a20e00682116e2e027e3e1171d0d06803171611e3e2e1e010a20a01803800c08040040507060504e3e2e1e0a01c180c0b8780427809b8b8780be527e3e1e02d949b8f8b80ba527e3e2e12c941c1b0700138f884480706c3c205e1e01023801a0850d06803805f8f849b8b8058742a0400d0d06803010a81003001808000f8440607030102e010199a16138f8b8782705046260e3e1179e16138f8b87819a7160685e3e2e1e0842298168e8a8680109c8678584e3e2e1e09c14118d878b805a78584e3e2e1e0679c14118d8985819e7170785e3e2e1e0842180105040301e2e0169c18168a80138f845c80705a3a104e2e016238f8b8780991264544e3e2e1e0a69d15138f8b87809a7809b8b8780bf12627e3e1e02dc4989b8f8b80bb12627e3e2e12cc4989c9b8f8b87831272726e3e2e1e0449e80147868814128e8a86829a7a705a3a2a1a004262198118985802d9c784e2e1e08b96138b87822d9a667046261600b661d98118d8580299c784e3e1e08a96138f8782299a667046361600a661d98158d8980259c785e3e2e08996178f8b82259a6670563626009661d98158d8984219c785e3e2e18896178f8b86219a6670563626108661e063618a00189822820800e00780144849c127878018487801c0878010300144849814484026840008f80284048b8028407021e007801a3068e1c0060c0878012322c00e8a1e00688127c0260f001811012585121009614486025448800006305881e08458478f8b87811042811e3e244e1e0101c006c5c2c1c00fc41c1f170f07003710706c5c3c2c00ec41c1f170f0b04331070706c3c2c1c0c49c1f170f0b070019108e08401711e3e2e1e04410a05b8f8b81138440707c6c3c2c118c41c0c0045f8f8b851380407c706c3c2c019c41c0c00780100017160706e3e2e1e0442702104a10a841c0250a841c0848700803a00412802c0250a801c0048c87003008b008030010125e3e2e090938b87824e3e2e1e086961e1b8f8b878268786e3e2e1e098978f8b86424e3e1e0908c5c44571f178b878298785e3e2e1961e178f8b865e2e1e0e385978b8782178e522161114c6c5e3e1e0a61a178f8b8258685e3e2e0978f87838a165e3e1e085e2949f8f8782426e2e1e0938f8b87809a526e2e1e02f949f8f8780b6526) else (if i < 7 then 0x858d84206845840200016100844422004018216064341101010404109e20426885c999c3171688589e98310040801045c40c4012244e30841181031004891388210042322111e189831047040c8b802e007801e007801e004100c08040014447050302010004101e082063628a061608a007066425e3e2e1e0a01c1985838f884678786e3e2e1e0649c401c1018178f8b8780907066524e3e2e1e0a01c198d8b87804278786e3e2e1e0659c441c1418138f8b8780923e0088780246049e127878018687801e0061a1e00780111100504e3e2e1e046270010604100c08040018587c5e2e1e01194180c08040010407e2e1e06317119a03c2661e0e2e39b801a0870c1e004438f87809b885873a2462e0e1e39a010070604e3e2e1e08526801076463626118129c1d918d898461987076663626118129f8e163628a0018d86280581c1814138f8b878096004401058478f8b87809c9c5e3e1e011941c0c08040010407e3e1e0621611985c58438f8b878046880f89f85838f8a6e006821e004438b87809f8c5c74342a00d0d0a803c2061d802866008060860806087081004038f884463b2463e1e0e29a0100486e3e2e1e08522801066463626019139c19918d8980659c7670663626019139f8a163628a00189822805c1c1814138f8b878096007801e00516127049e1e006161e007021e0040c0051612605161009a100021e00a141e006141e08458438f8b87811446810e1e045e3e2111c006c4c2c1c00fc51c1f130f07003714706c4c3c2c00ec51c1f130f0b043314707c4c3c2c1c00645201c1b0f0b0703167e08401710e3e2e1e04511a302105a30a8c1c0848c8b003a20416882050302010006161f138f8b80425060302010005111f8f8b81845c42680f4998f8b83866e006821c10780111e3e2e126e0161ce09789838f866821580284600a158210300007060504e3e2e1e0a01c17838b878e60605030201e0101c98138b8f83849471319e22625e3e09e00704e2e3e0e1251f801a087801c10706116e2e1e025e3111e8110211070605e3e2e1e0842680107656361601a149c1d958d85806998707666361601a149c581c18178f8b878210960041c1004038c084474705e1e3e0e2441c506b851d138f8270605e1e3e0e2441c978f8b8781126144744e3e1e0a59c4c98978f8b8312782801801e9a8e86806a947a00786161608a0018d86282080011051610e3e2e1e02727138f8b84425070302010005111f8f8b858058426171611e3e2e1e010a203f27e362e1e09b801a08780111e3e2e027e1171d068100341a0400f0013925e361e2e09a007060504e3e2e1e0a01c140c0b84004072704e3e2e1e0251c48638c9c978b8678018138f8b878094785600a118028560840c00605e1e3e0e2980e00682141a0400f021e00700117e3e1e025e21 else 0x5811604441421004084414224868680210040896163620812106258818922118446106e3110c138c5c31687068c938e205e308441a247a3a18c421412326e38a158d8a34785048c16105845818903118446107e2110c1388583e3e2085c1e1a324e288178821107881818705e38d1a8a8231085048c9f8a28563628d1a141234605e28c16105845c1c90311050801144c50c42110841b8440305e1170c5a1c1a325e188138421006891e8e8631105848c9b8628461608d1c161230785e38c1e138632584440c4443063e1078811110a28d128a226c18816125e1084016204841211606250c1211126050c42110841f8040305e0160f878021707868c9782204e008401e246a2a08c441612327e08a11858234605848c4443023e0078c11110a38c1610685e28c1a138232584440e118e206c0889780210058844150500406061c138638604e08e198e20662889e1918304c0881286204841211707250c1211127050c4011004401c210060b8f8421707089a100401c2e2e0085c1e0a004a2a0085818227)))
def layer255r9 : Packing := (691,3,5,63,0,15,1,packed255r9)
def keys255k10 (i : Nat) : Nat := (if i < 1 then 0x7659b8b0c7ae15c0f996a6d39000059186564448525000000253ca86754a0000000400400069c40000000000681f47d8903e337671029000140b00009e7326ea573712e30d3405c7f7b606cd9a88116684d11c38f0c1d9db99f0001971f778d3221f0d68c3d0420249b81b34a554c214066b26c9d66d7fcde567db2108132d9890e60bff6d7da7e17a221c8e2da018c908688ec21f5847e7811a0136073ba48c5b7d7ce2c9a0b70d35e231c9a3ed6fe0a2957840c61a4c7351fc1a4118650f37c0000b5fd223aa1b8f770b45aec675a8fc7e3663b0a0000373c000753d27900021e3f4f427be20c99bc039153149e808f74c0e68477453703767f191fa1b29398ccf02666530b3d183408c5a0000892a01591387665d5292915fc7ec45651055c0000000047afaa8c5cd98a63a48b709b8000f234d16ca3310793f66b2000000003b3c8f529757200014ffb51c55d000060d0001d22000085c00031b927b09ea000181ff2841036a134d44952ea6031825b14dd97b74934c004b8150f4fc538f56ccf3210a94eb2e84a3da84206f6e81fad2a281622b64b8626a112e06898821b80ef07d40000001a53b0091bb672103f000281747e6a4491d2422c5c11bd57162a48ac400019735c24abb5c33ab110e30da6a213d5a099572288c31e60c84b3eaa00008eeb0c4a1ca56384df84ca0232f417890f06220a1e697b85a68bb4c423f72cd4c37a1741eb1a990a333a24901bc2abd860000968be6179836502a6992d14aaa98c956125069403e551a8c413445fcf8f2cab519f9be485e63448521350003a35e803615772765fc50dc32077d08cd4c0976d7cd03871b78272506ea00a52d550084c894977d0de2d2085112696ee544447890a98f96be296881500abaa518285d7a9d00b80003583dd67597807d21c4cd715102a50be02b94674fb8a0683571565fdc92e1994907c140002548c3eb2a5d47e11065e5c48f054e0af410df709a250113280007918627338000092ab8a6d4ac00000035ad000096a9073a1ee3555d436c00004811167664257d655c1093223a5ef3595053804000529cc8af074000a4d04e400015924698d8d961e93af203d8c427d09d286a969da8fcd2503d0bba9faa67593568de20a0464397843d261989e2d438524680080014008100000a0c0c10916344940254080021468b049c107261018430d40800638002001800306080ab200c02ebe4118d0608901069c79402000021200580022c1281a1c00a361450700102ba0004184242000088107060413380521410d441848706040020018526000cc0406340830c594810a243050e105120610611082c0150000181080c180166cf800a44180000028b001c59700240030604f020c6c003008c1a01d740951a10002063c102160070006000d9021df800018585001cb01060008c else 0xc2baa6242a751e22f824f7a9d04ad148000868e2922784d205998000a4000008838636264fa0309bd66400014106718c750001cd9f38400096f2dda2181670000000084a000088b608b7a7157732b122ef748564a2f00007652c1864f9277d7615e6765aa456948000b89267a537c000f42f4c8b06647127938c553c20c2fa426890000000f83c0000003a8aa1df9b7b0100000000c26a24c915587485b00000000002d420000000f7c85e051c0000000369900029080000a2a94cc03d00911ca55589f4636e58645bf29bf272c3bb0cd4da49d205d819a07e84535835244000f734e6dd7054996a55643b6798dd90c0000246b1622a7f051918891cf7b8000000000073d85b8c58dd1b338a9dd86c5ceac3e1da82a38cb133c918097c4954e35e273c370000100ddb641909400000000a25ed5a0001c9028bee519280a7c0003d0658a2dd7c253e72d33e825589a1cb177268385658968616184351428297a3e9365eacd800025cc81eccebd848440c25683af3c65172115c9e262ee6c75fa237d12c974863bdefc7f864ca293cedd019231f74496116ad18152bf5b379d6e5ad18d99ac1af669dac11aaf48f4fec8f7dacd32707692d9e9e08a7e20c39e8deb3f3dd00ab656b13a227da96396c95100000000000308da917822c65e65f92fe958081b16044fb4ee88eb34c44e4549e800002c5947a400011e3db402e5225632f484c2c194be433d4d48e905f0003121d04c62b876f41200032af0000c7900dc000e8e)
def packed255r10 (i : Nat) : Nat := (if i < 1 then 0x5b695e253a93f24be9202442902e3c68dea33c8c162ab89b62218772190854a114835a098818602a7fcdfae7dddf407b99ea8798de17772dd7f74cdcf572ddc7970edbef6ea9b6c6c81adb6a75a5868699ce667996e64f98f262d186f60a97fa5ef178c5d7171e5b816945959618574d59c555d50b52e147a50f13f74ec937b4cd93064b21298496922347951b545dd13943ed0bd41c50333fd4fb03dc8f2d3bd8eb139e8e2e376cd9d357cd1a3370c973148c1b2f58b9f2d4cb002b08a6f28c49f326b897724c88fb232c88d217481f1fa07aa1de873c1c146c71a4065218505d6166055a14704de12d448c118c43a10443e10ec43810d443280be02cf0a7c26f08fc21607981bd063415d04d010b03880b9024006000c0000ffe885dbff60576ffc815dbff60176ffc805dbff9de66ffe885c7ff61971ffc865c7ff5d971ffe665c7ff60171ffc805c7ff99871ffe88587ff61d61ffc87587ff9dd61ffd76587ff5c561ffd80587ff20161ffe77187ff9de11ffd76847ff1da11ffe66847ffa2170ffd865c3ff21970ffd765c3ff99970ffd815c3ff20570ffd715c3ff58570ffc615c3ff84570ffe661c3ff58470ffc611c3ff84470ffe88583ff61d60ffc87583ff9dd60ffd76583ff60560ffc81583ff5c560ffc71583ff58560ffe11583ff5c160ffe77183ff5c460ffc71183ff84460ffe88443ff61d10ffc87443ff9dd10ffd86443ff21910ffd76443ff1d910ffe66443ff5c510ffd61443ff5c110ffd60443ff9dc10ffd76043ff1d810ffe66043ff9de00ffd76803ff1da00ffe66803ff5c600ffc71803ff58600ffc61803ff84600dfc869df7f20677dfc809deffa2176dfe775daff60476bfd801dbbf21e66efe7799bbf20666efc8099b7f9de66efd7699affa2171dfe775c7bf99971bfd861c7bf99871bfd801c6ffa2161bfd875877f9dd61efe66587fd5c561bfd871877f9dc61bfd80187fd21e11ff677847fd21a11ff576847fd1da11ff666847fd20211dfe77847bf99a11ff571847fd58611bfe885c37f9dd70efe665c37f5c570ff6115c2ff61870efe661c2ff60470ff6111c2ffa2160bfd875837f9dd60efe66583bf58560ff611583fe5c160bfd871837f9dc60bfd81183fd84460bfe88442ff61d10dfe77442ff61910efe66443fd84510bfd870437f9dc10bfd86043bf99810ff887803fe9de00ff886803fe5da00ff876803fe99a00ff881803fe5c600ff871803fe58600ff861803fe84600dfe77803bf99a00ff611803fe5c200ff960803fe44200cfd761dadf61476bbd841daf760c76bed821dafd60476bf9801db3f9de66bed821c77d5c471bdd83187bd58461df677847bd99a11bbd841c37e5c070b7d85183be580609fd87042bf61810b7d85042ef61010bdd83042fb60810ff1100437e9de00efa66803fc84600 else (if i < 2 then 0x1c0131e2235464c1c263c417061215474e18263c4170e0215260b8f161c09e2505cb45c78b0e0894278b8f161c09a2509c2e3c587026894464d152e3c587027895070d152e3c587044a43c5c78b0e0889a88e9e2a5c78b0e04d12a8c98287c18b0e3894878d8f161c1112d11d3850d871e0c51298e1b1e2c382225a23a78c9b1e2c3812c4a83e2c18f0a6983e2c18f0a5983e2c18f0a4982842e5a3c6c78b0e0a83c5891b1e2c38284a108870d8f161c14854840386c78b0e0a4363c38b0279a325498f161c09e80d8f0e2c09660d8f0e2c09264f16263c587046a12a40e1b1e2c38280c10b918f17062c38ea8d103c5c18b0e3a23868b13062c38e84c10b600a1f1e2c34868f8f161c11670c908600e171e2c348708588c68b871e0c5516229c2468a5f0e0c78ab0f1a2c4c38f062a23c40d170e3c18a80c9c3c62387063c54a7085f0850d8f160a43c6c78b0e08b38748430860b8f160a42e1c18f12799345498f161c09e80b87063c49a64e982a4c78b0e0a1385c78b0e04d3a78a931e2c381350170e0c78924c9e344c78b0e08b4474d131e2c3822d0992070b83161c742748182e1c78315018297211e262c7830d51a287898b1e0c34470d16262c7830d011285885f160c78698f182c4c58f061a13052d88207c7870521a3e3c5870449c3252388384c787052163e3c5870449c3852c42344c78b0e0a8b104e163442f8f161c15878d16263c5870511e286898f161c14044a16216c787160a63c60b131e2c38280c9c3c6218f161c14a70a5f1840d8b0e0a43c6c78b0e0893874a47186098b0e0a42c6c78b0e0893870c44845898f161c1511209c345885f160c786b0f1a2c4c78b0e0a08900e9a2c42d8f0e2c15c70d16263c5870511e305898f161c14270c5c284c78b0e0a43c5c78b0e0893874c58284c78b0e0a4345c78b0e089384c78b0e04f3264b131e2c3813d0131e2c38134c9d325098f161c1427098f161c09a74e96263c587026a0263c587025993a64a13062c38e8089f1e2c3812ce9d32509871e0c54044d8f161c09674e9a263c587025a13c68b8f161c11288e9a2e3c587044a23c64b8f161c11284c94384c58f061a13a50c131e2c38284e98284c78b0e0a31e2c38034a1b161c03e50f8f0e01b286c78b00e943e3c58464a1c363c58704c1c363c58704c9e363c58704c60385c78b0cc17161c18e532182e3c58260b8f0e0c52a78b8f161c13268b8f161c131a0e131e1c1304c78b06194d86098b0e098263c58704a14263c58704c14263c58704c13161c02e5098f0e015285c78b009942e3c58444b8f161c01254f131e2c38264d131e2c38264b131e2c3826bc56edeba9ee70b8e6dedb6bed71b4eaceeb2a6c6bb0d2bf6aee2b7aad0eafeaacaa66a8a29f1a6ce967a48a8e4a26285aa0727e59e667549c5a6df9a4e63997ee else 0xe1b1e1c580b4e95261c7831169c386c78b0e04b3a5498f161c05a70e1b1e2c38124f152c4498f161c09e3545c385c383163234174c930e0c58c8d0143e0c5871a69e2240e1b1600b87197a83c44817062c38d3525d324c18b0e3234070b83161c69270e931e2c381345a0b060b87063c44682c9d261c18f111a0286c38f0624f38688902e1c783127a62240e1b1e10b83116aa2240f87006c788291a8b2749871e0c44680c170e3c18924e19263c5870278b4464d11263c5870278b5070d11263c587045a43c4c78b0e08a9a88e9e224c78b0e04d16a2e1c263c583090a0ba64b8f160c2428081f163c18534f152870d8b004c784bd41e2a5098b1e0c29a92e992e2c783090a0384c58f0614b3c64c17160098f0872f5172c1c3050844863c18b0d85c826c58f0614b4464c103e2c7830a5a43a5c78b0e04d1282c463e1c783144a23a6c78b0e04b1280e9b1e2c3812c4a0b06098f161c04282c9d2e3c587010a0206c78b0e04f3868a94263c587027a62a50e1b1e1098b016a8b274b8f161c04280c131e2c3812ce5cb070c14211218b0e3c1616209f1e2c3812d11d385c784262c018b551d3840d8f161c09698a943e3c41b0e00842a0c971e2c3813c4a0b918d83161c71284f1b1e2c3812c4a1386c78b0e04b1280a131e2c38084e9d362c7830909c284c78b0e04f3c64c14263c587027a53a6c78b0e021385098f161c09a72e443860a10b10c78b0e0b08904f8f161c09a88e9c284c78b0e04d4c64c1c2e1c013163235474e182e))
def layer255r10 : Packing := (198,2,5,63,0,14,1,packed255r10)
def keys255k11 (i : Nat) : Nat := 0xfa6d17f0a9c2512dc3db6792ca0bc101eb38451ebfa6cd6213987e675f34d3fb8c50057fa0bcaa60375a5820a717c49a84a0b944841ba1fc1886f16932e7b243373aa72e68a0d508ab79884ab63c828bb4d0f50400079b25900052212b284000000d77915000331836270344e07e81066d4f65b957d9dc6100092a905000102b5400055300060c621d96b90c93e6b5ad0563a10006c5000eb0f1300016d445000487000b60e7936eba30007bd6b100000000024bb86e8f03de9ea4923e4a809133704d280bb54556bac4045875d767a8ec63ac4a104a273241dd52f4e97697bc2394c1a97c04ae3bb173f0ed8a35f89500082082c000426230dacd1ad7a000000164a83b2fe1112930174345e000000678b1ca7d419306497b140000004bce2d274000d24e46d47335e713658a455c8995be0b894216aa9f000989641a16298aaf12579cd09b85e94cb388b427d5088dd3b2a565f14d3c018601801800562e02500028024040519798820d0c000100001010054142900c76968100001530d6071c451c6c0
def packed255r11 (i : Nat) : Nat := 0x1851238a1807a051071a38a18281e38a18069871448e28601a81841c5822863a078e28601661c4185863822a068e28601661c61238a1805a061471228e08681e38a18049871461238a18281a38a18049871851238a18281638a18049871858e28601281e38a18251a38a18251638a18251238a1825dcb3cc4adca9a7c91a1c799b061950498f0318901b04809000ffcefff5dbfe3b7fe66ffae3ff1c7feb0ffc61ffc23ff5c3fe387fd60ff8c1ff443fe087fe00bfcefbf99bfb08ffa00
def layer255r11 : Packing := (20,1,5,63,0,10,1,packed255r11)
def keys255k12 (i : Nat) : Nat := 0x7ac0000000000112000000042e38cc94000028400000063453e3000000011000000000e80021d0c007100000000000000002980000b280001e8200bc0000000000000080
def packed255r12 (i : Nat) : Nat := 0x620824ff
def layer255r12 : Packing := (1,0,5,63,0,0,1,packed255r12)
def samples255 : Array (Bits × Bits) := #[(0x120300018060008700800f86072018000e4006b7133800267001fffffffff,0x120344418068908300a2428603201a4402522213011a48023490124924a49),(0xac000004800019f3000980183a2000c9800749eccfffd99fff4004007ff,0xac22200484440873112900080a2121c9891400244123488247492492126),(0x43000161700031e3c000e4861c44000f1fff98e70f000e1e0018007ff800,0x430a0b61714271c3c50ac482044450950a8598c70e512e1ca25a8a68b514),(0xfffe0c00018180003e03ffff0707e078000fe0001f07f0000fe0001fff800000,0xfffe0c00ab8180165201505b0707c0780a9fc0551e07e00b2fc0165c5b05a0b4),(0x700001fe00003ffc000007f8007ffff000001ff800000fffffe000000000,0x700c0dfe01833f78060c05a8004ce0e003061ff800618b77c3830c30c618),(0xffff800001ffffffc000000007ffff80000000001ffffffff000000000000000,0xffff8000cdab921b8000006c07ff7f000cc000661ffdbb8dc0001b006c06c0d8),(0xfffffffffe0000000000000007ffffffffffffffe00000000000000000000000,0xffff8c50f000001c000000700255fbb30f0af4786000000e00001c00700700e0),(0xfffffffffffffffffffffffff800000000000000000000000000000000000000,0x73af00546de02dfeaf80f800000070000380000000700000e00380380700),(0x0,0x0)]
def cols255 : IndexTree ColumnInfo := (.fork 16 (.fork 8 (.fork 4 (.leaf [(4,0,251,0,11),(8,0,247,0,11),(16,0,239,0,11),(32,0,223,0,11)]) (.leaf [(1,0,254,0,9),(2,0,253,0,9),(64,0,191,0,9),(128,0,127,0,9)])) (.fork 4 (.leaf [(5,0,250,0,8),(9,0,246,0,8),(18,0,237,0,8),(34,0,221,0,8)]) (.leaf [(68,0,187,0,8),(80,0,175,0,8),(136,0,119,0,8),(160,0,95,0,8)]))) (.fork 8 (.fork 4 (.leaf [(0,1,240,14,7),(0,2,204,49,7),(0,4,186,65,7),(0,8,118,129,7)]) (.leaf [(0,16,173,66,7),(0,32,93,130,7),(0,64,43,148,7),(0,128,23,104,7)])) (.fork 4 (.leaf [(6,0,249,0,7),(10,0,245,0,7),(17,0,238,0,7),(33,0,222,0,7)]) (.leaf [(72,0,183,0,7),(96,0,159,0,7),(132,0,123,0,7),(144,0,111,0,7)]))))
def levels255 : Nat → Packing
  | 7 => layer255r7
  | 8 => layer255r8
  | 9 => layer255r9
  | 10 => layer255r10
  | 11 => layer255r11
  | 12 => layer255r12
  | _ => emptyPacking
def index255 : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 13 49 5 10 6 0 keys255k8
  | 9 => lookupWord 130 443 7 13 9 0 keys255k9
  | 10 => lookupWord 230 783 7 14 10 0 keys255k10
  | 11 => lookupWord 66 226 6 12 8 0 keys255k11
  | 12 => lookupWord 6 59 2 9 5 0 keys255k12
  | _ => fun _ => none
def g255 : Forest := ⟨255,12,fun j => samples255[j]?.getD (0,0),cols255,#[[]],levels255,index255,noFactory,noFactorySound 255⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom23 : graphValid g23 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice23k3p0 : block g23 3 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK23k3 : block g23 3 0 1=true := slice23k3p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked23 : checkedTables g23 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g23 0 0 0=true)
  · exact (rfl : block g23 1 0 0=true)
  · exact (rfl : block g23 2 0 0=true)
  · exact layerOK23k3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low23 : Lower (vars 23) (graphGoal 23) 4 :=
  lower_forest (g:=g23) (i:=0) (hints:=65537) (before_sound [] baseKnown) geom23 checked23 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps23 : List (Nat × List Nat) := [(23,[]),(27,[50]),(43,[84,50]),(71,[100,84,33]),(77,[100,84,33,49]),(83,[100,65,81,49,16,32]),(85,[97,81,49,32]),(86,[97,16,80,65,33,48]),(139,[116,100,84,49,33]),(141,[116,100,84,49]),(201,[113,100,16,80,49,32]),(204,[113,96,64,81,48]),(210,[65,113,64,96,81,33,48]),(216,[16,113,32,98,81,48]),(240,[16,65,66,112,98,81,48])]
def known23 := extendKnown [] 4 maps23
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid23 : Known known23 := extendKnown_ok baseKnown low23 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom91 : graphValid g91 (boundsBefore known23) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice91k4p0 : block g91 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK91k4 : block g91 4 0 1=true := slice91k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked91 : checkedTables g91 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g91 0 0 0=true)
  · exact (rfl : block g91 1 0 0=true)
  · exact (rfl : block g91 2 0 0=true)
  · exact (rfl : block g91 3 0 0=true)
  · exact layerOK91k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low91 : Lower (vars 91) (graphGoal 91) 5 :=
  lower_forest (g:=g91) (i:=0) (hints:=67174401) (before_sound known23 valid23) geom91 checked91 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps91 : List (Nat × List Nat) := [(91,[]),(93,[100,33]),(103,[83,50,66,16]),(118,[65,83,97,16,32]),(155,[118,67,16]),(173,[116,100,84,49,33]),(186,[116,67,99,81,16,32]),(199,[100,116,84,33,49]),(203,[116,84,49]),(211,[100,116,65,81,16,48]),(217,[113,100,81,33,48]),(218,[116,64,97,80,49,32])]
def known91 := extendKnown known23 5 maps91
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid91 : Known known91 := extendKnown_ok valid23 low91 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known91) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice31k4p0 : block g31 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK31k4 : block g31 4 0 1=true := slice31k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked31 : checkedTables g31 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0=true)
  · exact (rfl : block g31 1 0 0=true)
  · exact (rfl : block g31 2 0 0=true)
  · exact (rfl : block g31 3 0 0=true)
  · exact layerOK31k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 5 :=
  lower_forest (g:=g31) (i:=0) (hints:=65537) (before_sound known91 valid91) geom31 checked31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(79,[100,84,33]),(143,[116,100,84,49,33]),(213,[48,112,32,99,33,81,64]),(214,[48,112,99,65,80]),(220,[16,112,67,97,80])]
def known31 := extendKnown known91 5 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid91 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom87 : graphValid g87 (boundsBefore known31) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice87k5p0 : block g87 5 0 5 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice87k5p5 : block g87 5 5 10 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK87k5 : block g87 5 0 15=true := (@block_merge g87 5 0 5 10 slice87k5p0 slice87k5p5)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice87k6p0 : block g87 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK87k6 : block g87 6 0 1=true := slice87k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked87 : checkedTables g87 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g87 0 0 0=true)
  · exact (rfl : block g87 1 0 0=true)
  · exact (rfl : block g87 2 0 0=true)
  · exact (rfl : block g87 3 0 0=true)
  · exact (rfl : block g87 4 0 0=true)
  · exact layerOK87k5
  · exact layerOK87k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low87 : Lower (vars 87) (graphGoal 87) 7 :=
  lower_forest (g:=g87) (i:=0) (hints:=33619969) (before_sound known31 valid31) geom87 checked87 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps87 : List (Nat × List Nat) := [(87,[]),(205,[100,116,84,33,49])]
def known87 := extendKnown known31 7 maps87
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid87 : Known known87 := extendKnown_ok valid31 low87 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known87) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice111k6p0 : block g111 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK111k6 : block g111 6 0 1=true := slice111k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0=true)
  · exact (rfl : block g111 1 0 0=true)
  · exact (rfl : block g111 2 0 0=true)
  · exact (rfl : block g111 3 0 0=true)
  · exact (rfl : block g111 4 0 0=true)
  · exact (rfl : block g111 5 0 0=true)
  · exact layerOK111k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=34603009) (before_sound known87 valid87) geom111 checked111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(111,[]),(123,[83,66,16]),(159,[118,84,50]),(183,[118,67,82,16]),(222,[32,112,16,98,50,81,64]),(238,[112,98,81,64]),(245,[96,50,115,33,65,80]),(249,[32,48,99,49,114,65,80])]
def known111 := extendKnown known87 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid87 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom219 : graphValid g219 (boundsBefore known111) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice219k6p0 : block g219 6 0 6 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice219k6p6 : block g219 6 6 9 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK219k6 : block g219 6 0 15=true := (@block_merge g219 6 0 6 9 slice219k6p0 slice219k6p6)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice219k7p0 : block g219 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK219k7 : block g219 7 0 1=true := slice219k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked219 : checkedTables g219 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g219 0 0 0=true)
  · exact (rfl : block g219 1 0 0=true)
  · exact (rfl : block g219 2 0 0=true)
  · exact (rfl : block g219 3 0 0=true)
  · exact (rfl : block g219 4 0 0=true)
  · exact (rfl : block g219 5 0 0=true)
  · exact layerOK219k6
  · exact layerOK219k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low219 : Lower (vars 219) (graphGoal 219) 8 :=
  lower_forest (g:=g219) (i:=0) (hints:=872480769) (before_sound known111 valid111) geom219 checked219 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps219 : List (Nat × List Nat) := [(219,[])]
def known219 := extendKnown known111 8 maps219
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid219 : Known known219 := extendKnown_ok valid111 low219 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom95 : graphValid g95 (boundsBefore known219) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice95k7p0 : block g95 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK95k7 : block g95 7 0 1=true := slice95k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked95 : checkedTables g95 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0=true)
  · exact (rfl : block g95 1 0 0=true)
  · exact (rfl : block g95 2 0 0=true)
  · exact (rfl : block g95 3 0 0=true)
  · exact (rfl : block g95 4 0 0=true)
  · exact (rfl : block g95 5 0 0=true)
  · exact (rfl : block g95 6 0 0=true)
  · exact layerOK95k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low95 : Lower (vars 95) (graphGoal 95) 8 :=
  lower_forest (g:=g95) (i:=0) (hints:=33619969) (before_sound known219 valid219) geom95 checked95 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps95 : List (Nat × List Nat) := [(95,[]),(119,[83,66,16]),(175,[118,84,50]),(187,[118,67,82,16]),(207,[100,116,84,33,49]),(215,[115,32,83,33,97,64]),(221,[114,48,99,33,81,64]),(237,[112,49,98,81,64]),(246,[96,114,50,65,80]),(250,[32,16,97,114,65,80])]
def known95 := extendKnown known219 8 maps95
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid95 : Known known95 := extendKnown_ok valid219 low95 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom127 : graphValid g127 (boundsBefore known95) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice127k8p0 : block g127 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK127k8 : block g127 8 0 1=true := slice127k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked127 : checkedTables g127 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g127 0 0 0=true)
  · exact (rfl : block g127 1 0 0=true)
  · exact (rfl : block g127 2 0 0=true)
  · exact (rfl : block g127 3 0 0=true)
  · exact (rfl : block g127 4 0 0=true)
  · exact (rfl : block g127 5 0 0=true)
  · exact (rfl : block g127 6 0 0=true)
  · exact (rfl : block g127 7 0 0=true)
  · exact layerOK127k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_forest (g:=g127) (i:=0) (hints:=34668545) (before_sound known95 valid95) geom127 checked127 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(191,[118,84,50]),(253,[67,113,96]),(254,[16,66,82,50,97,112])]
def known127 := extendKnown known95 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid95 low127 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom223 : graphValid g223 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k6p0 : block g223 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k6p1 : block g223 6 1 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK223k6 : block g223 6 0 2=true := (@block_merge g223 6 0 1 1 slice223k6p0 slice223k6p1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k7p0 : block g223 7 0 43 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k7p43 : block g223 7 43 44 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK223k7 : block g223 7 0 87=true := (@block_merge g223 7 0 43 44 slice223k7p0 slice223k7p43)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k8p0 : block g223 8 0 20 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k8p20 : block g223 8 20 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k8p84 : block g223 8 84 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k8p148 : block g223 8 148 60 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k8p208 : block g223 8 208 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k8p272 : block g223 8 272 39 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK223k8 : block g223 8 0 311=true := (@block_merge g223 8 0 272 39 (@block_merge g223 8 0 208 64 (@block_merge g223 8 0 148 60 (@block_merge g223 8 0 84 64 (@block_merge g223 8 0 20 64 slice223k8p0 slice223k8p20) slice223k8p84) slice223k8p148) slice223k8p208) slice223k8p272)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k9p0 : block g223 9 0 7 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k9p7 : block g223 9 7 22 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK223k9 : block g223 9 0 29=true := (@block_merge g223 9 0 7 22 slice223k9p0 slice223k9p7)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice223k10p0 : block g223 10 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK223k10 : block g223 10 0 1=true := slice223k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked223 : checkedTables g223 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g223 0 0 0=true)
  · exact (rfl : block g223 1 0 0=true)
  · exact (rfl : block g223 2 0 0=true)
  · exact (rfl : block g223 3 0 0=true)
  · exact (rfl : block g223 4 0 0=true)
  · exact (rfl : block g223 5 0 0=true)
  · exact layerOK223k6
  · exact layerOK223k7
  · exact layerOK223k8
  · exact layerOK223k9
  · exact layerOK223k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low223 : Lower (vars 223) (graphGoal 223) 11 :=
  lower_forest (g:=g223) (i:=0) (hints:=838926337) (before_sound known127 valid127) geom223 checked223 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps223 : List (Nat × List Nat) := [(223,[]),(239,[118,84,50]),(247,[83,66,16]),(251,[118,67,82,16])]
def known223 := extendKnown known127 11 maps223
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid223 : Known known223 := extendKnown_ok valid127 low223 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom255 : graphValid g255 (boundsBefore known223) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k7p0 : block g255 7 0 21 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k7p21 : block g255 7 21 18 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k7 : block g255 7 0 39=true := (@block_merge g255 7 0 21 18 slice255k7p0 slice255k7p21)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p0 : block g255 8 0 6 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p6 : block g255 8 6 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p70 : block g255 8 70 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p134 : block g255 8 134 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p198 : block g255 8 198 25 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p223 : block g255 8 223 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p287 : block g255 8 287 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p351 : block g255 8 351 39 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k8 : block g255 8 0 390=true := (@block_merge g255 8 0 351 39 (@block_merge g255 8 0 287 64 (@block_merge g255 8 0 223 64 (@block_merge g255 8 0 198 25 (@block_merge g255 8 0 134 64 (@block_merge g255 8 0 70 64 (@block_merge g255 8 0 6 64 slice255k8p0 slice255k8p6) slice255k8p70) slice255k8p134) slice255k8p198) slice255k8p223) slice255k8p287) slice255k8p351)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p0 : block g255 9 0 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p64 : block g255 9 64 6 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p70 : block g255 9 70 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p134 : block g255 9 134 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p198 : block g255 9 198 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p262 : block g255 9 262 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p326 : block g255 9 326 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p390 : block g255 9 390 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p454 : block g255 9 454 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p518 : block g255 9 518 9 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p527 : block g255 9 527 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p591 : block g255 9 591 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p655 : block g255 9 655 36 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k9 : block g255 9 0 691=true := (@block_merge g255 9 0 655 36 (@block_merge g255 9 0 591 64 (@block_merge g255 9 0 527 64 (@block_merge g255 9 0 518 9 (@block_merge g255 9 0 454 64 (@block_merge g255 9 0 390 64 (@block_merge g255 9 0 326 64 (@block_merge g255 9 0 262 64 (@block_merge g255 9 0 198 64 (@block_merge g255 9 0 134 64 (@block_merge g255 9 0 70 64 (@block_merge g255 9 0 64 6 slice255k9p0 slice255k9p64) slice255k9p70) slice255k9p134) slice255k9p198) slice255k9p262) slice255k9p326) slice255k9p390) slice255k9p454) slice255k9p518) slice255k9p527) slice255k9p591) slice255k9p655)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k10p0 : block g255 10 0 28 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k10p28 : block g255 10 28 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k10p92 : block g255 10 92 22 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k10p114 : block g255 10 114 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k10p178 : block g255 10 178 20 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k10 : block g255 10 0 198=true := (@block_merge g255 10 0 178 20 (@block_merge g255 10 0 114 64 (@block_merge g255 10 0 92 22 (@block_merge g255 10 0 28 64 slice255k10p0 slice255k10p28) slice255k10p92) slice255k10p114) slice255k10p178)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k11p0 : block g255 11 0 4 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k11p4 : block g255 11 4 16 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k11 : block g255 11 0 20=true := (@block_merge g255 11 0 4 16 slice255k11p0 slice255k11p4)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k12p0 : block g255 12 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k12 : block g255 12 0 1=true := slice255k12p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked255 : checkedTables g255 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0=true)
  · exact (rfl : block g255 1 0 0=true)
  · exact (rfl : block g255 2 0 0=true)
  · exact (rfl : block g255 3 0 0=true)
  · exact (rfl : block g255 4 0 0=true)
  · exact (rfl : block g255 5 0 0=true)
  · exact (rfl : block g255 6 0 0=true)
  · exact layerOK255k7
  · exact layerOK255k8
  · exact layerOK255k9
  · exact layerOK255k10
  · exact layerOK255k11
  · exact layerOK255k12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 13 :=
  lower_forest (g:=g255) (i:=0) (hints:=839974913) (before_sound known223 valid223) geom255 checked255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[])]
def known255 := extendKnown known223 13 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid223 low255 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exactLower : ∀ t, PEqualNP.MetaComplexity.HasCircuitSize 8 edge8444 t → 13 ≤ t :=
  conclude8444 (root_index (g:=g255) (before_sound known223 valid223) geom255 checked255 (k:=12) (by decide) (i:=0) (by decide +kernel))

end PEqualNP.Outside.L_meta_8443

theorem PEqualNP.Outside.L_meta_8443 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)) t → 13 ≤ t := PEqualNP.Outside.L_meta_8443.exactLower

import PEqualNP.Defs

-- The Live/Run/Forest checker derives from PressF10, pequalnp-proofs PR 4332,
-- and its extension in L_meta_3853, licensed under Apache-2.0.
namespace PEqualNP.Outside.L_meta_10968
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
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 4 &&& x 7) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 5 &&& x 8)
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
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 4 &&& x 7) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 5 &&& x 8)
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

def edge10969 : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8)
def sample10969 (r : Row) (i : Fin 9) := bit r (inputs.getD i.val zero)
theorem raw10969 : List.ofFn (fun i : Fin 9 => inputs.getD i.val zero) = vars 511 := by decide +kernel
theorem samples10969 (r : Row) : List.ofFn (sample10969 r) = (vars 511).map (bit r) := by
  rw [←raw10969,List.map_ofFn]
  rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem edge10969_table : ∀ r : Row, bit r (graphGoal 511) = edge10969 (sample10969 r) := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem conclude10969 (absent : Impossible (graphGoal 511) 14 (vars 511).toFinset) :
    ∀ t, PEqualNP.MetaComplexity.HasCircuitSize 9 edge10969 t → 15 ≤ t := by
  intro t hs
  obtain ⟨C,hf,hsize,correct⟩ := hs
  by_contra! bad
  have hp : proper (graphGoal 511) := by unfold proper; decide +kernel
  have he : (execute C.gates (vars 511)).getD C.output zero = graphGoal 511 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute C.gates (vars 511)).getD C.output zero) = bit r (graphGoal 511)
    rw [←b_read,execute_bits _ _ _ (fun g hg => (hf g hg).1),←samples10969,edge10969_table]
    exact correct (sample10969 r)
  have hout := get_rep (execute C.gates (vars 511)) C.output
  rw [he] at hout
  obtain ⟨k,u,S,hk,run,sub⟩ := extract C.gates _ hf hp (hout.resolve_right (fun h => h hp))
  have all : ∀ a ∈ vars 511, Essential (graphGoal 511) (vars 511) a := by
    have valid : checkEssential (graphGoal 511) (vars 511) (graphPairs 511 8607786324) = true := by decide +kernel
    have ident : (graphPairs 511 8607786324).map Prod.fst = vars 511 := by decide +kernel
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
def packed145r3 (i : Nat) : Nat := 0x7
def layer145r3 : Packing := (1,0,0,63,0,0,1,packed145r3)
def samples145 : Array (Bits × Bits) := #[(0x3f,0x49),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc7,0x92),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff24),(0x0,0x0)]
def cols145 : IndexTree ColumnInfo := (.leaf [])
def levels145 : Nat → Packing
  | 3 => layer145r3
  | _ => emptyPacking
def index145 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g145 : Forest := ⟨145,3,fun j => samples145[j]?.getD (0,0),cols145,#[[]],levels145,index145,noFactory,noFactorySound 145⟩
def packed102r3 (i : Nat) : Nat := 0xf
def layer102r3 : Packing := (1,0,0,63,0,0,1,packed102r3)
def samples102 : Array (Bits × Bits) := #[(0x0,0x0),(0x7fc1f,0x11c43),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb07e0,0xb556a),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc07ff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff48294),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffee318),(0x0,0x0),(0x0,0x0)]
def cols102 : IndexTree ColumnInfo := (.leaf [])
def levels102 : Nat → Packing
  | 3 => layer102r3
  | _ => emptyPacking
def index102 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g102 : Forest := ⟨102,3,fun j => samples102[j]?.getD (0,0),cols102,#[[]],levels102,index102,noFactory,noFactorySound 102⟩
def packed147r4 (i : Nat) : Nat := 0x1f
def layer147r4 : Packing := (1,0,0,63,0,0,1,packed147r4)
def samples147 : Array (Bits × Bits) := #[(0x87ff,0x191a3),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0f860,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5bb6a),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff007f,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6224c),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80,0x84410),(0x0,0x0)]
def cols147 : IndexTree ColumnInfo := (.leaf [(2,0,145,0,4)])
def levels147 : Nat → Packing
  | 4 => layer147r4
  | _ => emptyPacking
def index147 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g147 : Forest := ⟨147,4,fun j => samples147[j]?.getD (0,0),cols147,#[[]],levels147,index147,noFactory,noFactorySound 147⟩
def packed181r5 (i : Nat) : Nat := 0x3f
def layer181r5 : Packing := (1,0,0,63,0,0,1,packed181r5)
def samples181 : Array (Bits × Bits) := #[(0x3003ff3c03ff,0x10250b1c4913),(0x0,0x0),(0xcc0300cfff00,0x4d1746451f4a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0ffc00f003ff,0x1045814e0922c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000fffc00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb26098bae0b0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeeb82e00300c0),(0x0,0x0)]
def cols181 : IndexTree ColumnInfo := (.leaf [(0,4,145,32,5)])
def levels181 : Nat → Packing
  | 5 => layer181r5
  | _ => emptyPacking
def index181 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g181 : Forest := ⟨181,5,fun j => samples181[j]?.getD (0,0),cols181,#[[]],levels181,index181,noFactory,noFactorySound 181⟩
def packed110r4 (i : Nat) : Nat := 0x1f
def layer110r4 : Packing := (1,0,0,63,0,0,1,packed110r4)
def samples110 : Array (Bits × Bits) := #[(0x0,0x0),(0x1903fe703f,0x9090e3083),(0x6e03039fc0,0x2e4b4a94d2),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8ffc03e000,0x8b1c1be28a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00003ffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd090914b2c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff74e2e00c30),(0x0,0x0),(0x0,0x0)]
def cols110 : IndexTree ColumnInfo := (.leaf [])
def levels110 : Nat → Packing
  | 4 => layer110r4
  | _ => emptyPacking
def index110 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g110 : Forest := ⟨110,4,fun j => samples110[j]?.getD (0,0),cols110,#[[]],levels110,index110,noFactory,noFactorySound 110⟩
def packed227r4 (i : Nat) : Nat := 0x3f
def layer227r4 : Packing := (1,0,0,63,0,0,1,packed227r4)
def samples227 : Array (Bits × Bits) := #[(0x6dc1fb060,0x24cc7b56a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff927e0ffff,0x46211a3),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe3800c07f,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe3a94cc5c),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000ff80,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc294ee18),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb3180810),(0x0,0x0)]
def cols227 : IndexTree ColumnInfo := (.leaf [(32,0,195,0,4)])
def levels227 : Nat → Packing
  | 4 => layer227r4
  | _ => emptyPacking
def index227 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g227 : Forest := ⟨227,4,fun j => samples227[j]?.getD (0,0),cols227,#[[]],levels227,index227,noFactory,noFactorySound 227⟩
def packed362r5 (i : Nat) : Nat := 0x82000200080902000608020080200803e3968c57294884f19283c50500fd43fd42fd32fd41fd31fd21fd40fd30fd20fd10be44de33ee22f611fa00
def layer362r5 : Packing := (15,1,3,63,0,7,1,packed362r5)
def keys362k6 (i : Nat) : Nat := 0x94363100b38cc51880a239bbce07ad00aa30d0e
def packed362r6 (i : Nat) : Nat := 0x23444bf
def layer362r6 : Packing := (1,0,3,63,0,0,1,packed362r6)
def samples362 : Array (Bits × Bits) := #[(0x0,0x0),(0x680c0180ffff,0x2a1d10a246a3),(0x0,0x0),(0x900ffeff0180,0x10543a870d8a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1ff0070001ff,0x110e06714291c),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00007fffe00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc4824558b050),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeef0b8060c060)]
def cols362 : IndexTree ColumnInfo := (.fork 2 (.leaf [(2,0,360,0,4),(8,0,354,0,4)]) (.leaf [(32,0,330,0,4),(64,0,298,0,4),(256,0,106,0,4)]))
def levels362 : Nat → Packing
  | 5 => layer362r5
  | 6 => layer362r6
  | _ => emptyPacking
def index362 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 5 18 4 8 4 0 keys362k6
  | _ => fun _ => none
def g362 : Forest := ⟨362,6,fun j => samples362[j]?.getD (0,0),cols362,#[[]],levels362,index362,noFactory,noFactorySound 362⟩
def packed179r5 (i : Nat) : Nat := 0x104813048100401007cca8794280fe44fd42fd40fd20be44ee22fa00
def layer179r5 : Packing := (7,1,3,63,0,6,1,packed179r5)
def keys179k6 (i : Nat) : Nat := 0x5a0000300018c000e066a5d0001
def packed179r6 (i : Nat) : Nat := 0x6a47f
def layer179r6 : Packing := (1,0,3,63,0,0,1,packed179r6)
def samples179 : Array (Bits × Bits) := #[(0x60101fcf01ff,0x213142c72493),(0x901fe033ff80,0x10b0e1910f8a),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1fe0003c01ff,0x112c28538492c),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000003ffe00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeb0b162ef070),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffecc0c18008040),(0x0,0x0)]
def cols179 : IndexTree ColumnInfo := (.fork 2 (.leaf [(0,32,145,2,5),(32,0,147,0,5)]) (.leaf [(1,0,178,0,4),(16,0,163,0,4),(2,32,145,0,4)]))
def levels179 : Nat → Packing
  | 5 => layer179r5
  | 6 => layer179r6
  | _ => emptyPacking
def index179 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 23 1 7 3 0 keys179k6
  | _ => fun _ => none
def g179 : Forest := ⟨179,6,fun j => samples179[j]?.getD (0,0),cols179,#[[]],levels179,index179,noFactory,noFactorySound 179⟩
def packed302r5 (i : Nat) : Nat := 0x3f
def layer302r5 : Packing := (1,0,0,63,0,0,1,packed302r5)
def samples302 : Array (Bits × Bits) := #[(0x0,0x0),(0x20b0609c1f,0x31b9728e53),(0xc07fe7e0,0x1c123a462),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0ff80f800,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc5d386f94a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc60204518c),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000,0x382c580210)]
def cols302 : IndexTree ColumnInfo := (.leaf [(2,0,300,0,5)])
def levels302 : Nat → Packing
  | 5 => layer302r5
  | _ => emptyPacking
def index302 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g302 : Forest := ⟨302,5,fun j => samples302[j]?.getD (0,0),cols302,#[[]],levels302,index302,noFactory,noFactorySound 302⟩
def packed119r5 (i : Nat) : Nat := 0x7f
def layer119r5 : Packing := (1,0,0,63,0,0,1,packed119r5)
def samples119 : Array (Bits × Bits) := #[(0x1e46798003b00c03fff,0xe4239a901b52d49553),(0x20799fffccc00fff300,0x88a83c4c0641f30a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc79e1e0070fff003c00,0x429e1e1b50d370dbc3a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff81fe0007f000003fff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01dc0527e0a4292aac),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000007ffffffc000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbd6000602b2c8b200c0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7757c000f03c00f0),(0x0,0x0),(0x0,0x0)]
def cols119 : IndexTree ColumnInfo := (.leaf [(0,1,102,16,5)])
def levels119 : Nat → Packing
  | 5 => layer119r5
  | _ => emptyPacking
def index119 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => samples119[j]?.getD (0,0),cols119,#[[]],levels119,index119,noFactory,noFactorySound 119⟩
def packed311r6 (i : Nat) : Nat := 0x7f
def layer311r6 : Packing := (1,0,0,63,0,0,1,packed311r6)
def samples311 : Array (Bits × Bits) := #[(0x16001f98003b00c03fff,0x16920b9a501b52d49553),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff980199e004cc00fff300,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff998799e6344cc671f3ca),(0x1e1ffff0fff003c00,0x6a0a83d0d0701bc0a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe001fe0007f000003fff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe125f404a7e0a4292aac),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000007ffffffc000,0x22380000c2b2388e0030),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddc15f570000c03000c0)]
def cols311 : IndexTree ColumnInfo := (.leaf [(0,1,294,16,6)])
def levels311 : Nat → Packing
  | 6 => layer311r6
  | _ => emptyPacking
def index311 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g311 : Forest := ⟨311,6,fun j => samples311[j]?.getD (0,0),cols311,#[[]],levels311,index311,noFactory,noFactorySound 311⟩
def packed413r6 (i : Nat) : Nat := 0x7f
def layer413r6 : Packing := (1,0,0,63,0,0,1,packed413r6)
def samples413 : Array (Bits × Bits) := #[(0x183b00c00000fffffff,0x81b22c88021548d523),(0x0,0x0),(0x264cc00fff300cc03300,0x2244c0e43f315cc5b31a),(0x3870fff003c00f003c00,0x2850d0f03bc15f05bc1a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc07f000003fff0003fff,0x407e0441115460112a4c),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000003ffffffc000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbf00088222a98aa60090),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd5ab2f0bc00e003800e0)]
def cols413 : IndexTree ColumnInfo := (.leaf [(0,256,145,12,6)])
def levels413 : Nat → Packing
  | 6 => layer413r6
  | _ => emptyPacking
def index413 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g413 : Forest := ⟨413,6,fun j => samples413[j]?.getD (0,0),cols413,#[[]],levels413,index413,noFactory,noFactorySound 413⟩
def packed427r6 (i : Nat) : Nat := 0xe413f
def layer427r6 : Packing := (1,0,2,63,0,0,1,packed427r6)
def samples427 : Array (Bits × Bits) := #[(0x27580cc037380ff980,0x235a5cd3131a64f9aa),(0x38600f0049cff01fff,0x28621f11014a344aa3),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc1800ffff1f0001e00,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc4180d547f1f162de1a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fff0007e00001fff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd0188e0067e0142951c),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000007fffffe000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd40480246ca58b0050),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000,0x2be770ab800060c0060)]
def cols427 : IndexTree ColumnInfo := (.leaf [(0,1,298,128,5),(0,8,163,256,5),(1,0,426,0,5),(8,0,419,0,5)])
def levels427 : Nat → Packing
  | 6 => layer427r6
  | _ => emptyPacking
def index427 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g427 : Forest := ⟨427,6,fun j => samples427[j]?.getD (0,0),cols427,#[[]],levels427,index427,noFactory,noFactorySound 427⟩
def packed231r6 (i : Nat) : Nat := 0x90ff
def layer231r6 : Packing := (1,0,2,63,0,0,1,packed231r6)
def samples231 : Array (Bits × Bits) := #[(0xdb1ce03fe5980b0180,0x490c6387e599ab359a),(0x124273fc007fffc01ff,0x520c100a83c0483),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe38c7c00079e00ffe00,0x23847c99329e2ad562a),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0f800007e000fffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc0b81224560502a954),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000007ffff00000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff001b367f57c0f078),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb6f29c38000600c060),(0x0,0x0)]
def cols231 : IndexTree ColumnInfo := (.leaf [(64,0,167,0,5),(32,4,195,0,4),(128,1,102,0,4)])
def levels231 : Nat → Packing
  | 6 => layer231r6
  | _ => emptyPacking
def index231 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g231 : Forest := ⟨231,6,fun j => samples231[j]?.getD (0,0),cols231,#[[]],levels231,index231,noFactory,noFactorySound 231⟩
def packed437r6 (i : Nat) : Nat := 0x30aa479848c180cf95644e791233db95622f38ce22ed91211f988a11de95600f68ce00fc84600
def layer437r6 : Packing := (9,2,4,63,0,6,1,packed437r6)
def keys437k7 (i : Nat) : Nat := 0x39003015957635ecac58c8
def packed437r7 (i : Nat) : Nat := 0x7b6272e27b2272a26b225aa2a1018202002fcabbe44ef19fb88bec23fa00
def layer437r7 : Packing := (6,1,4,63,0,7,1,packed437r7)
def keys437k8 (i : Nat) : Nat := 0x2c30000d7c0003059
def packed437r8 (i : Nat) : Nat := 0x9175438260abf
def layer437r8 : Packing := (1,0,4,63,0,0,1,packed437r8)
def samples437 : Array (Bits × Bits) := #[(0xcc001e00030007ffcf001fff,0x4c848e4281084a42c7224913),(0x0,0x0),(0x3000067ffccc0060033fff800,0x10011a209c4c22e119108f84a),(0x0,0x0),(0xc3000780030fff8003c001fff,0x4310970851050b0853844922c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03fff80003f0000003fffe000,0x10142e00163b04c0262e1700b0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000003fffffffc0000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb823001182ea70538009804c0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeeebc05de0003801c000e00700)]
def cols437 : IndexTree ColumnInfo := (.fork 8 (.fork 4 (.leaf [(0,1,292,144,6),(0,4,145,288,6),(0,16,292,129,6),(0,128,292,17,6)]) (.leaf [(0,256,145,36,6),(1,0,436,0,6),(4,0,433,0,6),(16,0,421,0,6)])) (.fork 4 (.leaf [(32,0,405,0,6),(128,0,309,0,6),(1,16,292,128,5),(1,128,292,16,5)]) (.leaf [(4,32,145,256,5),(4,256,145,32,5),(16,128,292,1,5),(32,256,145,4,5)])))
def levels437 : Nat → Packing
  | 6 => layer437r6
  | 7 => layer437r7
  | 8 => layer437r8
  | _ => emptyPacking
def index437 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 3 11 2 8 4 0 keys437k7
  | 8 => lookupWord 2 11 0 7 3 0 keys437k8
  | _ => fun _ => none
def g437 : Forest := ⟨437,8,fun j => samples437[j]?.getD (0,0),cols437,#[[]],levels437,index437,noFactory,noFactorySound 437⟩
def packed183r7 (i : Nat) : Nat := 0x7f
def layer183r7 : Packing := (1,0,0,63,0,0,1,packed183r7)
def samples183 : Array (Bits × Bits) := #[(0x60013807f83b00c03fff,0x20131850581b12c49513),(0x9201cff804cc00fff300,0x120b4838344c0641f30a),(0x31c01f000070fff003c00,0x11c8bf232350d4711bc4a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc1ffe000007f000003fff,0x4162c00a0a7e024092a2c),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000007ffffffc000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffee13004c4c2b2b8ae00b0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbc9c0a7070000c03000c0),(0x0,0x0)]
def cols183 : IndexTree ColumnInfo := (.leaf [(4,0,179,0,7)])
def levels183 : Nat → Packing
  | 7 => layer183r7
  | _ => emptyPacking
def index183 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g183 : Forest := ⟨183,7,fun j => samples183[j]?.getD (0,0),cols183,#[[]],levels183,index183,noFactory,noFactorySound 183⟩
def packed430r7 (i : Nat) : Nat := 0x7f
def layer430r7 : Packing := (1,0,0,63,0,0,1,packed430r7)
def samples430 : Array (Bits × Bits) := #[(0x0,0x0),(0x340580c013fff9c07f,0x150da2d100aa38d123),(0x4c00600ffed980e7f80,0x4402e0643a598aa458a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe70807ff0071e00f8000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe5086e8f0771e1af8d1a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80ff800007e000fffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe8085008045a01050a14),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000007ffff00000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe2604c267f55c02c58),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000,0x12b78170b80006003060)]
def cols430 : IndexTree ColumnInfo := (.leaf [(8,0,422,0,7)])
def levels430 : Nat → Packing
  | 7 => layer430r7
  | _ => emptyPacking
def index430 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g430 : Forest := ⟨430,7,fun j => samples430[j]?.getD (0,0),cols430,#[[]],levels430,index430,noFactory,noFactorySound 430⟩
def packed243r7 (i : Nat) : Nat := 0x7f
def layer243r7 : Packing := (1,0,0,63,0,0,1,packed243r7)
def samples243 : Array (Bits × Bits) := #[(0x63180407f71e00f01ff,0x21084c50b30e4872493),(0x842407f809e7ff3ff80,0x42c3860221d10f8a),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff18c7f8000e7803c01ff,0x10844b0a14c70938492c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0f800000f8003ffe00,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0fac2c58f81c2ef070),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000ffffc00000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff02c2c58fdde00e070),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed6b3030600010008040),(0x0,0x0)]
def cols243 : IndexTree ColumnInfo := (.leaf [(32,0,211,0,7)])
def levels243 : Nat → Packing
  | 7 => layer243r7
  | _ => emptyPacking
def index243 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g243 : Forest := ⟨243,7,fun j => samples243[j]?.getD (0,0),cols243,#[[]],levels243,index243,noFactory,noFactorySound 243⟩
def packed490r7 (i : Nat) : Nat := 0x7f
def layer490r7 : Packing := (1,0,0,63,0,0,1,packed490r7)
def samples490 : Array (Bits × Bits) := #[(0x0,0x0),(0x418d018027ff980ffff,0x8543a200518a246a3),(0x0,0x0),(0xa61201ffdac06ff0180,0x22020a874ac528b158a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3863fe00e30070001ff,0x128221c0ce30c718311c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc07c0000fc007fffe00,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0789048b428554a850),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000ffff8000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00984cffae058b058),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed5dde1700030060c060)]
def cols490 : IndexTree ColumnInfo := (.leaf [(128,0,362,0,7)])
def levels490 : Nat → Packing
  | 7 => layer490r7
  | _ => emptyPacking
def index490 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g490 : Forest := ⟨490,7,fun j => samples490[j]?.getD (0,0),cols490,#[[]],levels490,index490,noFactory,noFactorySound 490⟩
def packed366r5 (i : Nat) : Nat := 0x4f57199953
def layer366r5 : Packing := (1,3,3,63,0,0,1,packed366r5)
def keys366k6 (i : Nat) : Nat := 0xc
def packed366r6 (i : Nat) : Nat := 0x80000000002479848c180bf99953cf95644bb58853bd58453be58053d795633e791233
def layer366r6 : Packing := (7,2,3,63,0,6,1,packed366r6)
def keys366k7 (i : Nat) : Nat := 0x6004ac4f60754c0008
def packed366r7 (i : Nat) : Nat := 0xa8420c321d44cb5306b2b210828d5311d4c475311c4372a1b1209007f957faa7fc53ff19df9577c89de33
def layer366r7 : Packing := (7,1,3,63,0,8,1,packed366r7)
def keys366k8 (i : Nat) : Nat := 0x1ccd004c000c99a4122
def packed366r8 (i : Nat) : Nat := 0x468897f
def layer366r8 : Packing := (1,0,3,63,0,0,1,packed366r8)
def samples366 : Array (Bits × Bits) := #[(0x0,0x0),(0x6805806001900ffe700ff,0x2a0da1684094250e34243),(0x18006007fe6e00c039ff00,0x804e052162e12c4a91312),(0x21007ff8018fff003e0000,0x102e8380c8b0701be0a0a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc1ff800001f000003fffff,0x410b00a029d02409142c2c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000001ffffffc00000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc4c04c13174b8ae00b0b0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb6f01705c000c03000c0c0)]
def cols366 : IndexTree ColumnInfo := (.fork 3 (.leaf [(2,0,364,0,7),(4,0,362,0,7),(8,0,358,0,7)]) (.leaf [(0,64,292,10,6),(64,0,302,0,6),(32,0,334,0,5),(256,0,110,0,5)]))
def levels366 : Nat → Packing
  | 5 => layer366r5
  | 6 => layer366r6
  | 7 => layer366r7
  | 8 => layer366r8
  | _ => emptyPacking
def index366 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 keys366k6
  | 7 => lookupWord 2 11 2 7 3 0 keys366k7
  | 8 => lookupWord 2 11 2 7 3 0 keys366k8
  | _ => fun _ => none
def g366 : Forest := ⟨366,8,fun j => samples366[j]?.getD (0,0),cols366,#[[]],levels366,index366,noFactory,noFactorySound 366⟩
def packed379r8 (i : Nat) : Nat := 0xff
def layer379r8 : Packing := (1,0,0,63,0,0,1,packed379r8)
def samples379 : Array (Bits × Bits) := #[(0x60ec0ac0003f30001e40ec00300033cc003ffff,0x606c0ad4a417352a0e406d52b54a11cd5495553),(0x30f43000333c000207330003fffccfffff3000,0x105430c0f33c306001130c193074454c1f330a),(0x0,0x0),(0x4308c0003c3ffffc79c3fffc000f0f0003c000,0x8c006d41501f42943407c01ef0f00dbc03a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff87c0f00003fc0000f81fc0000000ff00003ffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8780f0294be80a54f01f82a50a94ee02a92aaac),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800fffffc000000ffe000000000ffffffc0000,0xa8009c41f0000078ffe0003600d8bba83e000f0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000ffffffffffff00000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefa003180000c60bd6acb382ce000033000cc0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff57ff63be02beaf80000003c00f000003c000f00)]
def cols379 : IndexTree ColumnInfo := (.leaf [(0,1,362,16,8)])
def levels379 : Nat → Packing
  | 8 => layer379r8
  | _ => emptyPacking
def index379 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g379 : Forest := ⟨379,8,fun j => samples379[j]?.getD (0,0),cols379,#[[]],levels379,index379,noFactory,noFactorySound 379⟩
def packed375r8 (i : Nat) : Nat := 0xff
def layer375r8 : Packing := (1,0,0,63,0,0,1,packed375r8)
def samples375 : Array (Bits × Bits) := #[(0x607982c0003f30001e467980003b000c003ffff,0x603982d4a417352a0e4239aa901b552d5495553),(0x181f3000333c00020799ffffccc000ffff3000,0x80b30c0f33c30600088a983c4c3064c1f330a),(0x61e000003c3ffffc79e1e00070ffff0003c000,0x20a00006d41501f429e1e01b50d03700dbc03a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff87e01c0003fc0000f81fe00007f00000003ffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff87c01c294be80a54f01dc05527e0aa42a92aaac),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8001ffffc000000ffe0000007ffffffffc0000,0xa800044190000060bd60000602b20c8832000c0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000fffffffff80000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f4031e0000c78fff77567c000cf033c00cf0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff55f5fbbe02beaf80000000780000f003c000f00)]
def cols375 : IndexTree ColumnInfo := (.leaf [(0,1,358,16,8)])
def levels375 : Nat → Packing
  | 8 => layer375r8
  | _ => emptyPacking
def index375 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g375 : Forest := ⟨375,8,fun j => samples375[j]?.getD (0,0),cols375,#[[]],levels375,index375,noFactory,noFactorySound 375⟩
def packed477r7 (i : Nat) : Nat := 0x20080345037e55f78cffa00
def layer477r7 : Packing := (3,1,3,63,0,5,1,packed477r7)
def keys477k8 (i : Nat) : Nat := 0x20000b80000025
def packed477r8 (i : Nat) : Nat := 0x350eb37f
def layer477r8 : Packing := (1,0,3,63,0,0,1,packed477r8)
def samples477 : Array (Bits × Bits) := #[(0x180c7603b00180000f00007fffc3f3001ffff,0x8043601b21590a0050084aa42c173224a913),(0x0,0x0),(0x613187ccc001fffccccc006600333c0019800,0x211082c4c0fc87fccccc6ee637b33c1ed98fa),(0x81c21870fffe0000f0f00078003c3ffffe000,0x1400050d04e026050f022f811941508fe04a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0603e07f0000000f00ffff80003fc0001ffff,0x10203c07e0428214500550b00853e80449522c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff803ff800000000fff000000003fffffe0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff803ff800eb0758faf03cc01e62beaf7007b0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000000fffffffffffc0000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5f8000008c0460afaaa705538000098004c0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdeaf7d2b2f01780000038001c00000e000700)]
def cols477 : IndexTree ColumnInfo := (.fork 3 (.leaf [(0,4,217,256,7),(0,1,332,144,6),(0,128,332,17,6)]) (.leaf [(1,0,476,0,6),(16,0,461,0,6),(4,8,145,320,6),(64,256,145,12,6)]))
def levels477 : Nat → Packing
  | 7 => layer477r7
  | 8 => layer477r8
  | _ => emptyPacking
def index477 : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 9 0 6 2 0 keys477k8
  | _ => fun _ => none
def g477 : Forest := ⟨477,8,fun j => samples477[j]?.getD (0,0),cols477,#[[]],levels477,index477,noFactory,noFactorySound 477⟩
def packed443r7 (i : Nat) : Nat := 0x36c2a91e61230602ff3baa3cf95644ebcab19f9e448cfbb2ac23f58ce11ef4ab007ba44803ed19c01fc84600
def layer443r7 : Packing := (10,2,5,63,0,6,1,packed443r7)
def keys443k8 (i : Nat) : Nat := 0x16a00278c00010853c2ae01241000a028
def packed443r8 (i : Nat) : Nat := 0x71851038602c81c610384580e2071851030a140fb20ac71a28501203883871848450e02492ca1c61210e024938718512284380f2a884da218e884da22a21de61a7d08662409c42150781800ff957fd53ff547fd31ff543fd30ff4437e55ef913de33fd847fa00
def layer443r8 : Packing := (12,1,5,63,0,9,1,packed443r8)
def keys443k9 (i : Nat) : Nat := 0xf7000000001100004470000000000072cb0073c90000001a000000000000c5000000f806001
def packed443r9 (i : Nat) : Nat := 0x18a460d137f
def layer443r9 : Packing := (1,0,5,63,0,0,1,packed443r9)
def samples443 : Array (Bits × Bits) := #[(0x4c2b0003f30001b00027003ff33cc00ffff,0x442b22417322809022632288b11cc925493),(0x8710c00333c0002490039ffc00ccffffcc00,0x8510c60f33c618009616961d86445587cd8a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc18230003c3ffff38e003e00000f0f000f000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc082300ed4150ff38e177e1785ef0f076f07a),(0xe03c0003fc0003c0fffc000000ff0000ffff,0xa03c044be8045140b458045114ee0124a92c),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff003ffffc000003ff0000000000ffffff0000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd002710f00000e3ff0160016058bba8780070),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000003ffffffffffff0000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5a800880000882b649814982600002400240),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000,0x2f7d8ef02beaf00000e000e03800003800380)]
def cols443 : IndexTree ColumnInfo := (.fork 8 (.fork 4 (.leaf [(0,8,179,256,8),(8,0,435,0,8),(0,256,147,40,7),(1,0,442,0,7)]) (.leaf [(2,0,441,0,7),(16,0,427,0,7),(32,0,411,0,7),(256,0,179,0,7)])) (.fork 4 (.leaf [(256,8,179,0,7),(0,1,298,144,6),(0,16,298,129,6),(128,0,315,0,6)]) (.fork 2 (.leaf [(8,32,145,258,6),(34,0,409,0,6)]) (.leaf [(1,16,298,128,5),(128,1,298,16,5),(128,16,298,1,5)]))))
def levels443 : Nat → Packing
  | 7 => layer443r7
  | 8 => layer443r8
  | 9 => layer443r9
  | _ => emptyPacking
def index443 : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 3 15 3 8 4 0 keys443k8
  | 9 => lookupWord 4 37 1 8 4 0 keys443k9
  | _ => fun _ => none
def g443 : Forest := ⟨443,9,fun j => samples443[j]?.getD (0,0),cols443,#[[]],levels443,index443,noFactory,noFactorySound 443⟩
def packed491r7 (i : Nat) : Nat := 0x810000c1000000000000000cd82a4e90f1b305490f182430300bfceea1dfe77507dea1a837f9dd31bfae898fdd434c75f33489b799a33f3c8919eee6688bd722445f38ce22deccd08fb644847eb19c23f988a11
def layer491r7 : Packing := (16,2,4,63,0,7,1,packed491r7)
def keys491k8 (i : Nat) : Nat := 0x1bba9c80000ffa2b7ec00dc6401f312980144cfd492
def packed491r8 (i : Nat) : Nat := 0x128186aa190315522a08b50a359d071883530e941041a9874a082aac651062aa46390620aeb39883105559d241883558e418820aa07ac3586b0d61ac22e168ef55194411c0b74719478311306c2000ff593fd63ff50ffd62ff50bfd32ff587fd41ff4c7fd21ff846fe66ef913de33fb88bf611
def layer491r8 : Packing := (16,1,4,63,0,9,1,packed491r8)
def keys491k9 (i : Nat) : Nat := 0x3be91e73000090f586a8170100000dba7cdf523420fe1
def packed491r9 (i : Nat) : Nat := 0x8642b2ff
def layer491r9 : Packing := (1,0,4,63,0,0,1,packed491r9)
def samples491 : Array (Bits × Bits) := #[(0xc13cb2b0033000636e7003ffcac00c00cc00,0x411cb2b6373638212636398fcad96d96cd9a),(0x101c03cc003c00084939ffc000f000fffffff,0x14014c207c2080002920c82030824835483),(0x0,0x0),(0x22600c30003ffff18e3e00000f3fff000f000,0x2200030055505d08e3e0982653427026f02a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc380f03fffc0003e0fc000000fc000000ffff,0x428050310f800f3e0fc01b06cfc074074a87c),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00ffc00000003ff00000000ffffffff0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00fe80ca00ca2f7000d2348acb58b580350),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000003ffffffffff000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbea00008c008c3ded949c270002602600260),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbd5fafcef02af0000000e0380003803800380)]
def cols491 : IndexTree ColumnInfo := (.fork 6 (.fork 3 (.leaf [(1,0,490,0,8),(8,0,483,0,7),(32,0,459,0,7)]) (.leaf [(64,0,427,0,7),(256,0,235,0,7),(128,1,362,0,7)])) (.fork 3 (.leaf [(0,8,163,320,6),(0,256,195,40,6),(2,0,489,0,6)]) (.leaf [(8,256,195,32,5),(32,256,195,8,5),(64,8,163,256,5)])))
def levels491 : Nat → Packing
  | 7 => layer491r7
  | 8 => layer491r8
  | 9 => layer491r9
  | _ => emptyPacking
def index491 : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 5 20 2 8 4 0 keys491k8
  | 9 => lookupWord 5 20 4 8 4 0 keys491k9
  | _ => fun _ => none
def g491 : Forest := ⟨491,9,fun j => samples491[j]?.getD (0,0),cols491,#[[]],levels491,index491,noFactory,noFactorySound 491⟩
def packed431r8 (i : Nat) : Nat := 0xff
def layer431r8 : Packing := (1,0,0,63,0,0,1,packed431r8)
def samples431 : Array (Bits × Bits) := #[(0x13ac02b300cc00639ce700ffb32c0300,0x11ad16b346cd18218c634647b32d2b4a),(0x1c30033c00f00084e739ff00c3f003ff,0x1431073c42f10800a5294342c1710943),(0x2600003c000ffff18f83e0000fc3ffc00,0x2200027c00a542d08f83e1212d4344c12),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff380c003ffff0003e0ffc00000ffc00000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff280c077d51f007be0ffc03636ffc0e83a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00fffc00000003ff00000000ffffffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff400c45800140052f7000024242a88b22c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000003ffffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffea026000980263de5294b8b80002c0b0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000000,0x95f3b802ae0ab80000000c0c0000300c0)]
def cols431 : IndexTree ColumnInfo := (.leaf [(1,0,430,0,8)])
def levels431 : Nat → Packing
  | 8 => layer431r8
  | _ => emptyPacking
def index431 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g431 : Forest := ⟨431,8,fun j => samples431[j]?.getD (0,0),cols431,#[[]],levels431,index431,noFactory,noFactorySound 431⟩
def packed247r7 (i : Nat) : Nat := 0x8140102004000080100090f1b2a4878c0c0c02ff3bac39f99965dbccd19f5d658cf7b33423f58ce11df4cd0077965803ed19c01fc84600
def layer247r7 : Packing := (10,2,4,63,0,7,1,packed247r7)
def keys247k8 (i : Nat) : Nat := 0x9000015418a401001ce00003c488008c0000024
def packed247r8 (i : Nat) : Nat := 0x31071a9e6598648d523906b546a89c2baa122a4c3246aa1cc38d542a4838d54346b12e8a45658d62aa228d629e44dd4cb5120cbe4f180802000ff99bfd63ff587fd31ff583fd30ff442fe66df597de33fd847fa00
def layer247r8 : Packing := (12,1,4,63,0,9,1,packed247r8)
def keys247k9 (i : Nat) : Nat := 0xd500000816000017000000003100006490000000000092eb0000e90000003a0000000000a33
def packed247r9 (i : Nat) : Nat := 0x10862b2ff
def layer247r9 : Packing := (1,0,4,63,0,0,1,packed247r9)
def samples247 : Array (Bits × Bits) := #[(0x60d8300027003ff1e46798000ec00c00ffff,0x2048100a630a82b0e42398a406c52c525453),(0x8120490039ffc0020799ffff33000fffcc00,0x9016901c0600088a80f13006407cc0a),(0x319c18e003e00000c79e1e001c3fff000f000,0x119c08e477e4791e429e1e26d43537136f13a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc1e060fffc000000f81fe0001fc000000ffff,0x40a020b158015054f01dc0149f80a40a4a8ac),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe007f0000000000ffe000001ffffffff0000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffee00770980098260bd6000580acac8ac802c0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000ffffffffe000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800de00de378fff7757f0003f03f003f0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbd5b5e4e014e0380000000600003003000300),(0x0,0x0)]
def cols247 : IndexTree ColumnInfo := (.fork 6 (.fork 3 (.leaf [(0,4,211,32,8),(64,0,183,0,8),(0,64,181,2,7)]) (.leaf [(1,0,246,0,7),(16,0,231,0,7),(32,4,211,0,7)])) (.fork 3 (.leaf [(2,0,181,0,6),(128,0,119,0,6),(2,64,181,0,6)]) (.leaf [(1,16,102,128,5),(128,1,102,16,5),(128,16,102,1,5)])))
def levels247 : Nat → Packing
  | 7 => layer247r7
  | 8 => layer247r8
  | 9 => layer247r9
  | _ => emptyPacking
def index247 : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 3 20 2 8 4 0 keys247k8
  | 9 => lookupWord 4 37 1 8 4 0 keys247k9
  | _ => fun _ => none
def g247 : Forest := ⟨247,9,fun j => samples247[j]?.getD (0,0),cols247,#[[]],levels247,index247,noFactory,noFactorySound 247⟩
def packed445r9 (i : Nat) : Nat := 0xff
def layer445r9 : Packing := (1,0,0,63,0,0,1,packed445r9)
def samples445 : Array (Bits × Bits) := #[(0x62c0003b00180003300007fffccf3001ffff,0x22c8481b21590a0110084aa42c473224a913),(0x0,0x0),(0x9800004cc001fff0cccc006600333ffff9800,0x880011c4c04c827044cc22e611911508f984a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0e1300070fffe000cf0f00078003c3c001e000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0a1303dd0d0fe07ecf0f06ef837bc3c1ede0fa),(0x301c0007f0000000f00ffff80003fc0001ffff,0x101c1097e0428214500550b00853b80449522c),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc01ffff800000000fff000000003fffffe0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff401742e0000b0058fbb004c00262eea17000b0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000fffffffffffc0000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefc02300008c0460aeeaa705538000098004c0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000,0xb568bc02b2f01780000038001c00000e000700)]
def cols445 : IndexTree ColumnInfo := (.leaf [(8,0,437,0,9)])
def levels445 : Nat → Packing
  | 9 => layer445r9
  | _ => emptyPacking
def index445 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g445 : Forest := ⟨445,9,fun j => samples445[j]?.getD (0,0),cols445,#[[]],levels445,index445,noFactory,noFactorySound 445⟩
def packed439r7 (i : Nat) : Nat := 0x84f1b305490f182430300e3e6695644e5e6695633e9e6691233f1e5591233f2e5591222f4e558ce22f8e448ce22e7a6695600eba6691200f3a5591200f6a5588a00faa4488a00
def layer439r7 : Packing := (12,3,5,63,0,7,1,packed439r7)
def keys439k8 (i : Nat) : Nat := 0x304a00004700910000f900b6d3000000eba8345592438
def packed439r8 (i : Nat) : Nat := 0x91108314202301d14110407821890d1032c1a22110b85868841016186582a486220061440a002801830c2830c244902800c48414484140050a30a1c10a1c10a1c1091240a00291104b7044b70458215b3304733045330453704537045356608d6ccc11ccc114cc112d99823d1330c3af3b62b6a527995e4a8da29872087d1e074dbf6ad9e629765894e4e92d465053c4e4324b52848d1e45e10c2f06c00ffcaab27fe55913feb22a7ff91153ffcaaa17fd5350bfeb22a1ff91150ffa84a86fe66957bf2aac9ef95644efcab226fe6654fdf222a7f759233fbc8919f7e5550bef19a85fb95622fdaa7116fe66543df222a1fb88950ff2c9007fa44803fca14019f99a55d7ccd2273e559136f33467d795633f3c8919f6e5588bd722445f38ce22df4cd0077a55803dd22401fa88a00
def layer439r8 : Packing := (40,2,5,63,0,10,1,packed439r8)
def keys439k9 (i : Nat) : Nat := 0xf25c839d59d040029946644000300018a4d270001149f31f0b57400e3fa336dd3d3bd526800841a5428d20016478400460006801635c00f000045283003de000002080041211c800000a003487000
def packed439r9 (i : Nat) : Nat := 0x1036039214b42d80e94bb2020d9554203ce1544a04d116c8123e434c8144852ad80932554c80f50540d80e4452ec80836534c81444534c8134852ad80932554c80f4c534c813445495b203652544edb209884ad46c826510b6032544fb203654ceb60325bead6aca8e9aa4c8a204781bc661745412c420e4300961b04809000ff597fe55ff593fd54ff153fe44ff58ffd53ff50ffd52ff50bfd32ff583fd50ff503fd20bf99b7e55ef913de33fb88bfa00
def layer439r9 : Packing := (22,1,5,63,0,10,1,packed439r9)
def keys439k10 (i : Nat) : Nat := 0x110fa8000000000000000f8f14595200002cd81978b400e20013bc908d48000000000000000000000000d00000000e1d1ca6000052800000000000cb0000000009a2a
def packed439r10 (i : Nat) : Nat := 0x6b011ff
def layer439r10 : Packing := (1,0,5,63,0,0,1,packed439r10)
def samples439 : Array (Bits × Bits) := #[(0x262c0007e6000180009c007ff076003001ffff,0x222c8482e6428081098c8510b03644b224a913),(0x4393000667800024800e7ff800998003fff9800,0x4293181e678c1804b05a583b06898c1960f9b0a),(0xc00000787fffcc7000f800000e1fffc001e000,0x400011a82a09c47045f823046a1a11c08de04a),(0x0,0x0),(0x701c0007f8000307fff0000000fe0000001ffff,0x501c1097d0085105a16010a214fc0890449522c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff801ffff8000003f80000000000ffffffffe0000,0x800442e0000163b8098004c0985642e217000b0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000003ffffffffffff0000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffad402300001182f24e052704e000130098004c0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7bfbbc057d5e00007000380700001c00e000700)]
def cols439 : IndexTree ColumnInfo := (.fork 12 (.fork 6 (.fork 3 (.leaf [(2,0,437,0,9),(1,0,438,0,8),(4,0,435,0,8)]) (.leaf [(16,0,423,0,8),(256,0,183,0,8),(0,1,294,144,7)])) (.fork 3 (.leaf [(0,4,147,288,7),(0,16,294,129,7),(0,32,145,262,7)]) (.leaf [(0,128,292,19,7),(32,0,407,0,7),(128,0,311,0,7)]))) (.fork 6 (.fork 3 (.leaf [(17,0,422,0,7),(260,0,179,0,7),(1,128,292,18,6)]) (.leaf [(4,32,145,258,6),(16,128,292,3,6),(32,4,147,256,6)])) (.fork 3 (.leaf [(32,256,147,4,6),(128,1,294,16,6),(128,16,294,1,6)]) (.leaf [(256,32,145,6,6),(36,0,147,0,5),(129,0,294,0,5),(144,0,294,0,5)]))))
def levels439 : Nat → Packing
  | 7 => layer439r7
  | 8 => layer439r8
  | 9 => layer439r9
  | 10 => layer439r10
  | _ => emptyPacking
def index439 : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 4 22 3 8 4 0 keys439k8
  | 9 => lookupWord 13 57 6 10 6 0 keys439k9
  | 10 => lookupWord 7 61 1 9 5 0 keys439k10
  | _ => fun _ => none
def g439 : Forest := ⟨439,10,fun j => samples439[j]?.getD (0,0),cols439,#[[]],levels439,index439,noFactory,noFactorySound 439⟩
def packed494r6 (i : Nat) : Nat := 0x4a6008c00800008a06430426ca8f01575919dd5458eaf130aa2e031f4e611545c063f2aaa2c6b0a636cd921cd63582dab2239ac6b063721d634c960
def layer494r6 : Packing := (7,4,5,63,0,7,1,packed494r6)
def keys494k7 (i : Nat) : Nat := 0x1ec00000a98257c0389c0002
def packed494r7 (i : Nat) : Nat := 0x8103031e104140b18200140080c20b042020880200082140801cc6100000e18202102c48e10302031e10505088020008ec6141422084143430408083c10f04304302000850383462b0d17004280e4600591801240260060050085c00811008082000022a08a0301060c0a10a02040d1a00421c1130030ec8d01b002c00c3f1b406c00b0030fc6c31b00205002031c0040000600380080001c11505180c700100140e003800e002000000000000001800e002000000000001732df5b0b55652c3578ae55b2af558a954f297520a354327f4f89c5372674c09752b24b4889051b22f45089511217420814ff1f73e07a4f11df3b0744e11bb3606a4cf193308604bb16f2d8594af15b2a85349f1332584948d10f2103e4790eb1b8354670bf1702d4570ab1402744d097120224430831001c4370630c01642904b0881041f03b0700d41902f0580a41301f0300540900f01802403003000df5819dd639fd809dd63bf5819dd63d7e7755163f3d6455163df6771c563df5741c563f75541c563df5721c563df4715c163d7d545c463dfa885c063df9845c0639fe885c063b7e8858d53f748158d539fc87999439fc8799a339fc8759233f3d6455233d7e7754d629fd809dd32fd48158d32d7e7754d32d7d7654d32f5d6354d32f6d5358932d7e7755161f3d6455161e7d5458d61edd634c961d7e7755131d7d7655131f3d6455131f5d5458d31f5d6354d31f755458531f6d53589219fd839dd60bed821cd60bf5811cd60edc7358d60ef48158d609fc878cd609fc874c960edd634c960bdc835c560edd634c560bed8218d40bf58118d40bf98018d409fd869dd309fe885d930df4815d9309fc8799930ef963581309fd839dd209fc8758d209fc878cd20ef963581209fc8758d109fc874c910ef96358110bf9864c110e3e66591549f5819dd639ee885c863d6d545c863dae445c8639f6885c463d75545c463db6445c4639fa885c063d79545c063dba445c063e3e6691153b5c8755233e5e6655233f1d6455233e9e6691233e5e6654e33f1e4454e33be58118e22be98018e22e6e6654e22ece668ce22f4d538ce22ed56358531e766655211f356455211eb666912119f48758e11bb58418e11be58218e11bf18018e11e766654e11f364454e11ed6668ce11f55548ce11f96448ce11f55538ce11ee66688a11f655388a11fc63388a11eba6691200be98218e00bf18118e00eda668ce00f9a448ce00eea6688a00fca3388a00ef26684600fb24484600fd23384600fe22284600
def layer494r7 : Packing := (115,3,5,63,0,11,1,packed494r7)
def keys494k8 (i : Nat) : Nat := 0x709fa922c000f278419af2251b9710cd2e17d676e7944d0eb7e1cf60d8375db463b8afe0cbb50413d21c79a6f3c1ab8c686c81ea62c04172a1c3e121240cfd0d8fa23d9000002aedc873e00000000d68e8da0e45000000560ef08dc6847b27129a219bf1ba0757150e3d6aecb402cb2670cfed4e6ba0009b3386e1c0002f11c9000000cc8000018580024aeb5257db54c000100353bbe4595800669dcb3c6071de55646288b86b6a0000e81249c6bc004525bfc70e7dbe48404b1440c074229408328b4511c018500710661a01708da8f001102
def packed494r8 (i : Nat) : Nat := (if i < 1 then 0xf18f55784bb65d60e79732b8f1c5ee2270737e9b94db66d13639abcd51697b489a00cd766532bd90cc79628310d85ec146002f797a2baf5d12e1d6aeb4a59eacc160eafa56c2abd544a80539a961450a1b50727953869a14ca257527692e47f233914a89844221dd0b884841a209d0347dc3e41ed0f167773b19d3ce767273899b54d2e683337996cc8e6332fa974cb465882af9510a4450027292f092645c22410d08163f71e38ecc72236f19f8c586122f516d0b185722ac14f8a4850a27112408d04161cd0cb057c2a413e09884742120f507083341720ac04c02100ee06a02b012406a0210068003ff3bac7ff5d163ffac8b1ffd7258ffeb8ac7ff5c163ffccca1ffd6350fff33467ff59233ffac6b17fe3358bfeb1a65ff59161ffac6b0ffd43587feb12c3ff4c961ffac6a0ffd644c7feb1a63ff50d31ffac498ffd324c7feb1a43ff9dd60ffae6b07fc73583feb1ac1ff8cd60ffae4b07fd62583fe992c1ff5c560ffac2b07fd31583fe90ac1ff99940ffac6a07fc63503ff19a81ff58540ffa62a07fe774c3febb261ff1d930ffccc987fd634c3feb9261ff58930ffa64987fd714c3feb0a61ff4c530ffa42987fc73483feb1a41ff8cd20ffac2907fd31483feb1a21ff58910ffa64886fc7399b7f332c9df99954f7ccd225fe7758f7f332c7df55163f7c88b1ff47158fbeaa0c7ef91063bfae431dfd7118efeb80c7df99953efac8a9f7d6354f7f33287df54d43fb8ed19fde668cfeeb2467bf99a33efaa919fbe448cfeeb1c67f750e33bfceeb16fe6658bbea9ac5f78cd62bfcee995fd764cb7f33265f758d32efaa6997de334cbf6b1265fb99a22fdac7117ec6388bf719c457f9dd61dfcccb0f7d54587df222c3bf58d61efaa6b0fde33587f7112c3bf99941efaa6a0fde33506ff3ba637f5d931dfccc98f7d544c7df22263f758d31efaa698fde334c7f711263fd58531bfcee90dfd764877f332437f5cd21efaa690fde33487f6b1243fb4c921feac290ff666847fab2423fd58e11fe8c708ff543847fb19c23fd58a11fea6508dfe775837f332c1ef91160dfac6b07de33583f7112c1fd84560dfccca07de33503fb08a817f9dd30bfaec986fe664c3df22261f78cd30fdc44987f6114c3fcb02617f9dd20bfaec906fe66482feb9a41f78cd20fda64907ed21483fb08a41fe58120bfcee885fd764437f33221ef91110bfae6887de33442feb9221fb88910fea62887f521443fcb0221fe4c110ff4cd007f963803fc31c01fe8ce00ff2c5007f932803fcb0c01fe4c600ff2430067e665539eb22a9af99a44b7ae831ded7218efab88c77e5c063cfccca9f3e4454f6f33467d755233f3c8919f5d538cf7733445db54e22f9c67116f666847baaa423ed91211eeaa708fd633847f311423be99a00f7489007da33803f511401fc84600 else 0x70d1234512384923450a20512088384831a2831030d0220c111c090aa286186405c30e8a1c68e1445210458321182148411621113181110e8c648421448610444585081203ca861c2a1c0222c01074380c49211400c2070c16020952600a0230a015891608a022088c02918f0f00a94149480f00424324228028680324492034040485242a4401088a910040d82407211600e406c0187812234502447212600cb8b9100481202918022d220101084880884212200f162c90a87009101a2805650d101c041296880e015148c4802c4280a01090b82805040d00846843850d044991a289213cd001182c5070c142030582a8480284a544709005a3263c08a5191d4a88d284828230c1416016a460c14203c08854e30386080c115218145419223449e40c19129903451a911900c8a44f062051e149503450c0c0051c08a0208a3c21d8d4469a02089140090c008305058249799003088495124304560925640b24160172c307015931c7218a4a8950021f00612565800a28012180663808228580b10910031a129512420701085186890e12820342061030818e1a4a81a2c206160224240a101e0212c2063c252a24840e0290a38f121c250426400c204a06c01c84b8248f202059380809081161c290c124a0f1e4a821242043e0282c4c2983602108495183e02b2480b0014702281082430234290280822460a30460b141820305228808028120220b4360912c090140901409014090140901409010c1628384060a4503058a080e402c144090140901404014090140901152840c07c018450286959120604024c8163448080304024c82a2c4808030d2049511109905448901006203e02b2652830590902c80c101c2c04078080280802080c048282c04010b0c00248283404010629208088ca48202180f8044229318c022110960028a004860188d048091828c1440a205103264449f10c1322593822c46438631290d1905e20e1b0505740ad21c3609cae221a4386c13c8854c88b042a5444a70448144527045254452704582152a2253822510e0854e08a442a644582444a6445221befdf2ef617a3bcb5e0aecf74cb9c5c5adf76e0b62dac6d3b67bb33d94ec7f61db04d7d6bc35d4adcd65eb07561a9fd45aa054eea6d531a965497a3751328474019ec4eda7293799af4d0e65130d9794b425792a894349924772198f8471e33d17c8ad44e223b10987ac31617106c82c40f60530007ebbef1)
def layer494r8 : Packing := (218,2,5,63,0,13,1,packed494r8)
def keys494k9 (i : Nat) : Nat := 0x6b95c74d68c6a2519aa61a6972874bfd217b2949c0d0c3601ce645306f5f8b62be40ff7695493e00000032a000bbb8959a3fd95223ab77e2468c141f733c41442285a51000000a64db7c083bfac89c41d5a44c6200066a00000013010700088e90e000dcc000212c2cf6d09e46b000178fb047508bb48f72eca00d263966d01f1ca71231000a342b8a7442f3874a8610e09b4e3801243cf5aa0000925193a2d3b458039fa4465188c73dc3079ec5000d1e16ec5634f3b584ac1149040a90215c100e4de2776f59f68641de5200032bba60004320000006144b2fb154300076739942d000000a37518dd0fb4203f82349a5793c000000f97616a1388100013a540da7dbc23f00005048cccd77fd17f4c000d1565d00000077c6c2dae15500068db3685b0001b3d5969112ea1b96c71a4896ac4a5470a68183aadfd73cb198ed323d9d4f9c2c968a57d19354709d2d85a0eba80500b25e921429fbd826c5aa04784fa9835420d8fe7a79b896aaf4231d1d776a1b531380018005186c401020c021008c586823c01b0015f0e023d8001a10001087018c000000c02003800458f07040ccaf66000162e00098000c70252000041870020
def packed494r9 (i : Nat) : Nat := 0xcac54294c03d030f112c4a68438d4454c142a68342148f00d48e08d112c4c3c54214c034e317444bc04ce38d444ac04ce68e35015302142838c8044b139a38d4054c0a5038ca0544081340c3c113149138e30111241b38e34113149138e34112a41338e329004c528114d110f4c12c44911d11404c834549125110d4c12d11404c94054c1231152449051f83ba6fcd51922f4588a392f2283e4708c91622643d8690ba1381f82d03c03c003fe66ff593fd63ff18ffd43ff8cffd62ff4cbfd61ff507fd31ff487fd60ff503fd30ff483fd10bf99b7d54ef9137d53f78cfee22fd847fa00
def layer494r9 : Packing := (25,1,5,63,0,11,1,packed494r9)
def keys494k10 (i : Nat) : Nat := 0x397893035000036c000071302c8000b4012c0049be96ae5f3c8e0088adc00c312f41e6004043801891000d104
def packed494r10 (i : Nat) : Nat := 0x8124127f
def layer494r10 : Packing := (1,0,5,63,0,0,1,packed494r10)
def samples494 : Array (Bits × Bits) := #[(0x0,0x0),(0x20183401600c0010c9fffe19007ff9c01ff,0x81503682d040000550609412838d0483),(0xc260c001800ffe6cb6cc006e00600e7fe00,0x4220402b81642e2c92cc542e1562aa4562a),(0x113810801fff0018f38f0018fff800f80000,0x1280081ba0f01c8538f0348b0d81af8341a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe1c060ffe000001f03f0001f000000ffffff,0x214020854028051d02d00a1d02805050a854),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe007f000000001ffc00001fffffff000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe007e2601302617ac002c174b256402c160),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000001fffffffe0000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0027813c279ffffaaf800bc17802f178),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffda95db7805c0b800000030000c0180030180)]
def cols494 : IndexTree ColumnInfo := (.fork 13 (.fork 6 (.fork 3 (.leaf [(128,0,366,0,9),(0,128,364,2,8),(4,0,490,0,8)]) (.leaf [(8,0,486,0,8),(64,0,430,0,8),(2,0,364,0,7)])) (.fork 3 (.leaf [(32,0,462,0,7),(256,0,238,0,7),(2,128,364,0,7)]) (.leaf [(72,0,422,0,7),(0,4,202,288,6),(0,8,166,320,6),(0,64,292,10,6)]))) (.fork 6 (.fork 3 (.leaf [(128,64,292,10,6),(192,0,302,0,6),(12,0,482,0,5)]) (.leaf [(32,4,202,256,5),(36,0,458,0,5),(66,0,300,0,5)])) (.fork 3 (.leaf [(68,0,426,0,5),(256,4,202,32,5),(256,8,166,64,5)]) (.leaf [(260,0,234,0,5),(264,0,230,0,5),(130,64,292,8,5),(136,64,292,2,5)]))))
def levels494 : Nat → Packing
  | 6 => layer494r6
  | 7 => layer494r7
  | 8 => layer494r8
  | 9 => layer494r9
  | 10 => layer494r10
  | _ => emptyPacking
def index494 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 13 1 7 3 0 keys494k7
  | 8 => lookupWord 38 133 6 11 7 0 keys494k8
  | 9 => lookupWord 72 249 7 12 8 0 keys494k9
  | 10 => lookupWord 8 38 4 9 5 0 keys494k10
  | _ => fun _ => none
def g494 : Forest := ⟨494,10,fun j => samples494[j]?.getD (0,0),cols494,#[[]],levels494,index494,noFactory,noFactorySound 494⟩
def packed479r10 (i : Nat) : Nat := 0x1ff
def layer479r10 : Packing := (1,0,0,63,0,0,1,packed479r10)
def samples479 : Array (Bits × Bits) := #[(0x300983b3000facc0019800001b00000139ce000fff806765800330007ffffff,0x100881b30005acca1599428009000a1318c650a285802365944b32892aaa513),(0x480e0c03eccccf0001e0000024924001ce73fff0004999860003ffffe666000,0x80a04016ccccf060de0c1800092460b4a523071834889860c195183e66630a),(0x18130303c30f0f00001fffff338e38001f07c00000071e1f80003c0007878000,0x811010143050f000fca81ff338e381bbf07c0de06f71e1f803dbc07b78780fa),(0x201c040c03f00fffffe000003c0fc0001ff800000007e01fffffc00007f80000,0x14000003500f5404e00098140fc008bff800460235a01ae811c00237f8004a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0e007f003fff00000000003c00fffffe00000000007ffe00000000007ffffff,0x40a007e003ffa00142802851400b6d42c0000a1450a7fdc00289005125554a2c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0007fffc00000000000003fff00000000000000007fffffffffffff8000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0007bfe80000038b007163ebf0039300001c98e4c25765172e2ae5c0001cb0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000003fffffffffffffffffff800000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbe5f5000000000020c004182bf64921c0a5290e08700000004300086000010c0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7eafefebcaaf0abf0157e00000003e000001f00f800000007c000f800001f00)]
def cols479 : IndexTree ColumnInfo := (.leaf [(4,0,475,0,10)])
def levels479 : Nat → Packing
  | 10 => layer479r10
  | _ => emptyPacking
def index479 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g479 : Forest := ⟨479,10,fun j => samples479[j]?.getD (0,0),cols479,#[[]],levels479,index479,noFactory,noFactorySound 479⟩
def packed509r8 (i : Nat) : Nat := 0x61548f30918301cbe7799a44ecf3bc8919f3d9de66847d6ccd22423dd6778ce11fcb2246708f6e9de44803be4ef08c01fb24484600
def layer509r8 : Packing := (9,3,5,63,0,6,1,packed509r8)
def keys509k9 (i : Nat) : Nat := 0x412221e362d0d01b805c001
def packed509r9 (i : Nat) : Nat := 0x870051a404870049940522305223051818c0a1c0126501284c126066ccd586427ab0c6b566a8e6cbd58649b2f5464f5618d6acd5193d512d57aa3992f5619264bd51cc97aa3866057c5dd725b56a19b61d7357d524c1153e8d82f4a221c731603606c00efe7799bbf99974fde778cff75d233efe665c7f78cd71efe66507f78cd41ffa77803fe5d200ff971803fe50600cfe7799b6f9de44ebe66913779de33f9e448cf7d9de11ef666847ed91211fd6338477e9de00fba44803fc84600
def layer509r9 : Packing := (24,2,5,63,0,10,1,packed509r9)
def keys509k10 (i : Nat) : Nat := 0x16700084a4e546251d34e03547aa0a0b23c91d00040aae0086d139600c1f4c00400040018e00
def packed509r10 (i : Nat) : Nat := 0x941927892a914292071a2a63950a8ea881c68a98e542a3ea1e2a63948a91a238698a8927951aaaa2634caa59a39649e248faa9a2634baa5a239649e244eaa9a2630baa5f067ab92672301086012003ff3bffd74ffae3ff506ff3befe66f7c89f78cffb08ffa00
def layer509r10 : Packing := (10,1,5,63,0,9,1,packed509r10)
def keys509k11 (i : Nat) : Nat := 0x3085000000c40000000068a90000000000000021000000000000a700000000a60000830000000000000022000000000000
def packed509r11 (i : Nat) : Nat := 0x24e52206612a9ff
def layer509r11 : Packing := (1,0,5,63,0,0,1,packed509r11)
def samples509 : Array (Bits × Bits) := #[(0x600660ec1600000760000c00000601e066000003fffff87981f980000cf300007fffff,0x2002606c1640a903640aac81540200a0220102a55205583980b99052847320a92a4153),(0x0,0x0),(0x18098030f0000009980000ffffe1999819998000330000181f99e0000333fffffe60000,0x80880105000a638980a66414ce0999808998519730a33080b99e053191150a63e614ca),(0x210e00430980000e1fffff00000601e19e1e00003c000061e1e1ffffffc3c0000780000,0x10a0000098061ba1a061f00c3c200a19e1e03077c060f20a0a0a8307fc3c061b780c3a),(0xc030187c0e00000fe000000000181e01e01fffffc000007e01fe000003fc000007fffff,0x401018780e08152fc08154102a880a00a00aa0558040aa7c01f4020a53b8041525482ac),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffff01c01f800ffffff000000000001fe001ffe000000000007ffe00000003fffffff800000,0x101400a800ba159c000159802b31f6001f7600a660014cc77f40000ac62eea159c002b30),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe001ffff000000000000000001ffffe000000000000007ffffffffffc0000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe001ffff01d9e0001d9e03b3c1dff5e00007c7800f8f05f5f5f57cf80000f9e001f3c0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000001fffffffffffffffffff8000000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffbdefc0000011e000011e0023c017d5f55dd54f802a9f0000000004f0000009e00013c00),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffef6b5756fa45e000565e000bc000000000000700000e000000000070000000e00001c000)]
def cols509 : IndexTree ColumnInfo := (.fork 10 (.fork 5 (.fork 2 (.leaf [(0,64,437,8,10),(64,0,445,0,10)]) (.leaf [(0,1,364,144,9),(0,16,364,129,9),(0,128,364,17,9)])) (.fork 2 (.leaf [(1,0,508,0,9),(4,0,505,0,9)]) (.leaf [(16,0,493,0,9),(32,0,477,0,9),(128,0,381,0,9)]))) (.fork 5 (.fork 2 (.leaf [(8,64,437,0,9),(1,16,364,128,8)]) (.leaf [(1,128,364,16,8),(16,128,364,1,8),(4,32,217,256,7)])) (.fork 2 (.leaf [(32,4,217,256,7),(64,256,145,44,7)]) (.leaf [(256,4,217,32,7),(256,32,217,4,7),(260,32,217,0,6)]))))
def levels509 : Nat → Packing
  | 8 => layer509r8
  | 9 => layer509r9
  | 10 => layer509r10
  | 11 => layer509r11
  | _ => emptyPacking
def index509 : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 3 11 1 8 4 0 keys509k9
  | 10 => lookupWord 8 29 5 9 5 0 keys509k10
  | 11 => lookupWord 3 53 0 8 4 0 keys509k11
  | _ => fun _ => none
def g509 : Forest := ⟨509,11,fun j => samples509[j]?.getD (0,0),cols509,#[[]],levels509,index509,noFactory,noFactorySound 509⟩
def packed383r10 (i : Nat) : Nat := 0x1ff
def layer383r10 : Packing := (1,0,0,63,0,0,1,packed383r10)
def samples383 : Array (Bits × Bits) := #[(0xc0766056000001f598001980000f3200cecb000330000183b32c000c000fffffff,0xc0366056a54800b59a9559a95407320046cb552b35528081b32d552d5525555553),(0x1807a1800059999e0001e0000100393330c0003ffffe64cc3f0000ffffcccc000,0x802a18601d9999e180de180c000091130c30195301e244c170c064c07ccccc0a),(0x607800000061e1e00001ffffe603ce3c3f00003c0003870fc3ffff0000f0f0000,0x2028000031e0a1e000cca80ce2014e3c3f0031bc031a850d4340c700c6f0f00ca),(0x81804600007e01fffffe0000183c0fc03fffffc00003f80ffc00000000ff00000,0x46000dea01ea803e0003c8140b4035d007c0007bf80ffc00360036ff0003a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0fe007800007ffe00000000001fc00fffc00000000003fff00000000000fffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0fc007814a97ff40052a8052a9f800ffb800aa500aa53f7e0002aa42aa4aaaaaac),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00007fffff800000000000001ffff000000000000003ffffffffffffff0000000,0x1500004e20ce000000033000331dfeb0000000c6000c615ab2a8833883380000330),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000000000001ffffffffffffffffffc000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fd0018f000000063c0063c17ebf4aeca2cf82acf8000000033c033c000033c0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeadfd7b1df00155e157c0157c000000000000f0000f0000000003c003c000003c00)]
def cols383 : IndexTree ColumnInfo := (.leaf [(0,1,366,16,10)])
def levels383 : Nat → Packing
  | 10 => layer383r10
  | _ => emptyPacking
def index383 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g383 : Forest := ⟨383,10,fun j => samples383[j]?.getD (0,0),cols383,#[[]],levels383,index383,noFactory,noFactorySound 383⟩
def packed255r10 (i : Nat) : Nat := 0x1ff
def layer255r10 : Packing := (1,0,0,63,0,0,1,packed255r10)
def samples255 : Array (Bits × Bits) := #[(0x600d80c600000139ce0007ffe0f3200cecb000330000183b32c000c000fffffff,0x2004804200015318c6055015607320046cb052b30528081b32c152c1525554153),(0x80120109248001ce73fff8000100393330c0003ffffe64cc3f0000ffffcccc000,0x124800b4a52003800c000091130c00195001e244c1700064007cccc00a),(0x3199c0631c70001f07c0000000603ce3c3f00003c0003870fc3ffff0000f0f0000,0x1199c0211c728cbf07ca3328cc2014e3c3f0531bc531a850d4354c714c6f0f14ca),(0xc01e067c1f80001ff80000000183c0fc03fffffc00003f80ffc00000000ff00000,0x400a067c1f8183bff8060f183c8140b4035d307c0307bf80ffc0c360c36ff00c3a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01e007801fffffe00000000001fc00fffc00000000003fff00000000000fffffff,0x100a0028016d82ac00000aa02a9f800ffb8000a5000a53f7e00002a402a4aaa82ac),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0007ffe00000000000000001ffff000000000000003ffffffffffffff0000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffee0007dee00533000014cc5331dfeb000000ac600ac615ab2a8ab38ab380002b30),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000000000001ffffffffffffffffffc000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbff5f80000063c000018f063c17ebf4aeca2cf82acf8000000033c033c000033c0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefd5fb57bc927c00a529f007c000000000000f0000f0000000003c003c000003c00),(0x0,0x0)]
def cols255 : IndexTree ColumnInfo := (.leaf [(4,0,251,0,10)])
def levels255 : Nat → Packing
  | 10 => layer255r10
  | _ => emptyPacking
def index255 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,10,fun j => samples255[j]?.getD (0,0),cols255,#[[]],levels255,index255,noFactory,noFactorySound 255⟩
def packed507r7 (i : Nat) : Nat := 0x930c0a1eb714cceeb08c349d6e2999556118695adc533222c230d2e5b8a662258461
def layer507r7 : Packing := (4,5,6,63,0,5,1,packed507r7)
def keys507k8 (i : Nat) : Nat := 0x23300852000
def packed507r8 (i : Nat) : Nat := 0x820020000800000000000000000000000000000000000000000000000000000000000000000000000000000000000459158a3c8da308aa2487a1884a0c81a007e9f47b9e8789dc759d0729c46f9b86c9ac699a066994639886097c5d9705a964579585494c519404e9344b9284891c45910429043f8f83c8ec398e0368d4338c8308bc2d8b02a8a4278982488c218801e8741b8681885c15850128440f8380c82c09820068008ffaa898595718ffaa89859121f0f9de6695644f179de6695633f279de6691233f479de5591233f8799a5591233f8b99a5591222f339de668ce22f9399a558ce22fa399a448ce22fc3956448ce22c5fa667761461ccfa665561061e4f9de5561061acfaa98591061e4f9dd8591061e579de5560c61e679de4460c61ec79564460c61e5b9dd8588861aebaa98488861e6b9dd8488861ecb9558488861ecb6164488861e739dd8388861ed39558388861ee39118388861cbd6a29958461abd6a29958461d3da667758461d9da665558461f1d9de5558461dada664458461f2d9de4458461f8d9564458461db9a662258461f399de2258461f999562258461fa99122258461e5e9de5560061e6e9de4460061ece9564460061e7a9de2260061eda9562260061eea9122260061f1d9de6695611f2d9de6691211f4d9de5591211f8d99a5591211f359de668ce11f559de558ce11f9599a558ce11f659de448ce11fa599a448ce11fc5956448ce11f399de6688a11f9999a5588a11fa999a4488a11fc99564488a11f719de3388a11fb199a3388a11fd19563388a11fe19123388a11f1e9de6695600f2e9de6691200f4e9de5591200f8e99a5591200f569de558ce00f669de448ce00fc6956448ce00f3a9de6688a00f9a99a5588a00faa99a4488a00fca9564488a00f729de3388a00fd29563388a00fe29123388a00f3c9de6684600f5c9de5584600f9c99a5584600f6c9de4484600fac99a4484600fcc9564484600f749de3384600fd49563384600fe49123384600f789de2284600fb899a2284600fd89562284600fe89122284600ff08ce22846008bd6a29958461
def layer507r8 : Packing := (93,4,6,63,0,10,1,packed507r8)
def keys507k9 (i : Nat) : Nat := 0x40166831d9faae22ca940043d78247168fc5fa00201628933e2e01ca92843b5824011000613e5699c85b5ed5185056f3ac754d0abcdc0069aba8c9ec300033d712c7f1de49656d4a4b399ec7810008b46000032696ac2c5935200f33ccbb0a627f24084a297c97023000880000569831756a000758e6c001addd383000361f1bb1963400000e4765059800477cc19e1a0a5e5640a420050010410060050dc0001192801410410823406c1
def packed507r9 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0xf3bc88b07cf95644583bdcef112c1f6e5588960fd722444b077d9de11583eecab08ac1fb64484560ff311422b076f9de44543f5c89112a1df67784550fdb22422a87f988a11543afcef2aa81f6e5588940efb3bc22a07dd95611503fcc4508a81d7e7795530edf3bc88987cf956444c3bdcef11261f6e5588930fd7224449877d9de114c3eecab08a61fb64484530ff311422986fd26211483f6c8908a41d7e7795510edf3bc88887cf95644443bdcef11221f6e5588910fd7224448877d9de11443eecab08a21fb64484510ff311422887be99975802ff532b2c01dfa7759600fbcbaacb007de5da55803df4ccba401f7a555d200bfd4cac90077e9dd64803ef4aab24017fa9955200efd3baa9005fe65954803df4ccaa401fb96591200fecbac67007f65d233803fb2a919c01efa665ca00fed19ae5007ee91162803df4cca9401fba4454a00fed19aa5007be99942803f72c8a1401fda3350a00ff4b2c45007fa59222803fd2a911401efa665c600fbd2aae3007f68cd71802ff532b0c01dfa7758600f7cb2ac3007de95561803df2c8b0c01fba4458600ff5112c3005fea6551803bf4eea8c017f99654600f7d332a3007de59551803ef2a8a8c01fba4454600fed19aa3007fa88951802ff532a0c01dfa7750600bfccb283007be99941802ff32aa0c01f7a5550600fdcb2283007ee55141803fb466a0c01fea2250600f7d33243007ee91121803fb46690c01ff17684600ff8bac23007fc59611803fe2e908c01ff16484600ff8aa423007fc5ca11803fe2c508c01ff15284600ff8a14230077e9de11803df4cd08c01f7a5584600fdd22423007f68ce11803fd44508c01ff17184600ff8b0c23007fc54611803fe28308c01ff12184600e3f3bccd2af2f9de66913a7cef2ac89e3e6695644e6f3bccd19f579de558cfcbccd2ac67d9e7791233f4f3348919fc7956448cf9dcef33445e6e6695622f5733489117cb9564488bb9cef19c45ece668ce22fa72ac67117e39123388a6fd32c28c397e7761461cbec3caa30cefa658418737ceec20c3b3e5561061d9ec2c8830e779dd831876bcaac18c3b9e4460c61dd72230430edb6162218775b09110c3bcd8388861b7b4cac230f3d9dd61187cecaab08c3eb64458461f73112c230e7e9dd801876f4aac00c3bba4460061df51130030f3d9de66847aecef2ac23e766695611edb3bc8908fad99a44847e6cab22423dd6778ce11f6b3346708fd595633847f2c8919c23de67788a11f733344508fd995622847f4c8911423fc63388a11e7d3bccd0075e9de55803cf4cd2ac01dba7791200f5d33489007ce95644803bb4ef19c01f5a558ce00fcd224670077a9de22803dd4cd11401f6a5588a00fd522445007f28ce22803be4ef08c01ef26684600fb92ac23007ec91211803fa46708c01fe22284600 else (if i < 2 then 0x2c66b0fd795633587dbac919ac3f9e448cd61df744444b0f7b9de22587ddccd112c3eed6588961fb72ac44b0fbb59222587f5c89112c3fce3388961cff3bb0a30f5f9de551876fcaac20c3dbe7791061ddec2c8830fcf956441876fb0ab90c3bbd845c861deec1ae430f7b9de22187edcab110c3bed8488861fd72244430fbda6561187deb2eb08c3ef59258461f7ab92c230efe5c9801873fd113baa39fe7761951d7e4c4cca8ebfa22665479fcef332a3afd8699951ebf3bacaa8f9f99965547afceeaa2a3e7e6655151ddf44488a8f6f9de4454777b0d222a3ebe6691151f9eb2c88a8ef7a2233547bbcef19aa3bdd868cd51f6f33466a8fd759633547ebaa919aa3f9e448cd51f7733444a8feb91222547f9c67112a3afc9899941d7f444cca0f3f9de665075fb0d33283afe6661541dbf444aaa0f5f9de555076fb0d2aa83e7e6695541f5f332c8a0fcf95564507d7cccaa283bde888cd41eef3bc66a0ef761a33507dbccd19a83bdd858cd41faf2ac66a0fe759233507f3aa919a83bee8888941df6c3444a0fbb99a22507edcab11283fad6488941fd6aa444a0ff38ce22507afcef2aa63dbe7791131f9f2ac8898f7b9de224c7edcab11263fae4488931d7e4c4cc90cff262664867f930b2243ebe6691121f6f3346690fe791233487becee434237f4985da11f7a4c4cd08f7d9de66847deaed33423ef6665d611efb3bacb08fbd99965847ee90d2ac23f757695611fbb334ab08fbd99974847eecaaba423df67759211f7b332c908fdd95564847beceeaa423ef66655211fda4348908fed99a44847f6acb224237f4985ce11fbb2aae708f7d9dd63847eecaab1c23fb64458e11efb3baa708fed91153847beceea1c23f765550e11feabb46708ff55d633847faacb19c23fd5748ce11feab246708ff555233847decccb9423fd6335ca11bfa4c2c508fbd99962847f6c88b1423fd63358a11f7b332a508fed91152847fac66a9423ef66650a11feb19a8508dfd26132847f6c8899423fe48688a11ff33344508ff959622847fcac911423fe55488a11ff2b1c4508ff954e22847fca87114233fc985da11d7e4c4cd08f3f9de668467f93133423d7e7795611f3f334ab08f6f9de44847d7ccd22423f3e5591211eef3bc6708fb799a33847ebcab19c23f9e448ce119fe4c2c508f7b9de22847ddccd11423f6e5588a11fd72244508ff38ce22847decccb8c23f76555c611feb19ae308dfda6561847beceeb0c23ef66658611fbb2aac308fed91161847fac66b0c23fe62258611efb3baa308fbd99951847f6c88a8c23fd63354611ff3112a308f7d9dd41847deccca0c23f765550611feb19a8308ff988941847becee98c23f76554c611fdb2226308ff988931847deccc90c23fb64448611feb19a4308efd262115c3eecab08ae1d7e7795560ed else 0x893444c993084b19284499924848a920c47b91d046c919445d913443c90d442d908641590264020fd83ee8f9c3df8f603d08f243c18ed63b28ebe3ac8ea63a68e8e39c0e643960e4c38b8e1037c8dd43648d743558d383468cfc32e8c8a31b0c4e30c0c002f88bc42e98b522c40aaa2958a02270097e24f08fa22e08521ff87bc1de874a1c686ea1ae868a19206061710582150052213804c2120043e0ff03de0e7035a0ca82e80b282ac09a824c08b821007c81d406d819805e815c04b010e03c00d202d009601e005a00f001e0005ffa65655d37fd11332a97fe9955163bff4cac8a96ff65e885877fb2b442c3bfd94a2161dfec9510b0effa21755877fd10ba2c3efd655d161bfe4c2a8b0effa21545877fd10b92c3bfe8854961f7eb22a4b0effa21425877fd10b8ac3bfe885d951dff444cca8fdf5d9655477fd10ba2a3bfd865d151fbeb2ae8a8effa2164547efacab22a3f7e6655151dff442e6a8effa2163547efaa8b1aa3bfe8850d51bff4cac2a8effa22665077fcccc2a83bfe8859541fdeb2ac8a0fef999545077fd10b1a83bfd8558d41fdeaa2c6a0effa21535077fd10b1283fbd6458941dff442a4a0eff61952507f7ac8a9283bfe884c941bff4cac2a0dffa6561486ffd32a8ae17fe9955160bff4caa2b07df55151582ffd32a0ac17fd9550560fdeaa282b05ffa6541542ffd32a8a817fe9955130bff4caa2987df551514c2ffd32a0a617fd9550530fdeaa282985ffa65414839fcee40ccd6fd9520666b7eca1033367fa22775979fcef332cbe7e665d565f3e48ccd2af5f9de66957cfaed334abe7e6695574e7f3bcccb26dfa2255593afcef2aac9e7e6695564d7e4c4ccaa6bfa22665539fcef332a9afd8699954f5e48ccd2276f9de66912f7d32b2c89dbe7759644f5f332cb227cf99a55913afcef2aac7dbe7791163f9f2ac88b1f6f9de4454fafcef2aa87ede665d633bef4cacb19f779dd658cfebaeab2c67f5d7695633f6f332e919fd7955748cefbd32b2467dde7759233faf2aac919df7a65548cfbbceeaa4677dd9655233f6f332a919fe7596448cfdbccd19ae5ebe6691162fcf22466b17af99a4454bdbccd19aa5f9e448cd52f5f332c8a17b799a3350bf3ac919a85eec9199a22ef73bccd117bb9996588bedccd2ac457ee9959222f77332c9117db9556488bddcccaa445fae6691222fd6b2c891177b9dd6388bedcaab1c45fae4458e22fd7222a7117db9554388bf9acb19c45fcd648ce22fe6aa467116bf262665c67f931332e33fc9859571f3f334aab8fb799a335c7ebcab19ae39fe889dd61e7f3bcccb0ebfa21655879fceeb2ac3b7e8895561ebf3bcaab0f9f99a555875fd10b22c3cfe7759161f3f2aac8b0eefa2244587b7cef222c3ebe6691161f5eb2c88b0fcf956445877bd1119ac3dde778cd61f6eb)) else (if i < 4 then 0x405860b0c16182c105820b04162b04200000000061820000310158c2ae855d0e0280c08e5f09c6157c26e855f0e0280c08d62ae8a630cba19742b157446f85630aba10ec5a2b0a922d15854696492292a8f1455168ac2a41545a2b0a922d158546964aa2a38543a171c2a1d0b8e150e85c7178b42a2b13143a964aa2a44b255151a291c8b8e2d158a2d158a2d158a2d158a2d158a151085c70a8842e385442171c2a210b8f014060467187014060466e870140604780a03023c05018119be1c0501811e0280c08ce26e8b014060467184dd0e0280c08e5f09c6157c26e855f0e02197c32f865f09c4dd12be138c26e855f0e02157c38087010abe1c043557552d53ad4bb527547f518544350053d14ecd3954d953354c152e74a9526348cd20347951b5461516744dd107435d0a741950354014fd53e94f753d14f153b94ea33984e313804dd136ccd83354cd353414cd5324cc633084bdf2ebcb6d2cacafb2b2ca9b2964a17279c9a5258c933240c8e5231c8a9222c87f20f481f204c8071fa47dd1efc7a11e547771d6473b1c2c6ed1b846c31a946991a3465d18b45fd177c5c116445731554501138c4c5129c48911ac44d10bc4110f843c30e943870dec35d0cfc3210c0c2c10a4423d087c213081c1fb07741d106cc195062416b04ec10b036c0bd027c081018c045009bf42fa0be52f88bdf2f753dc8f663d56f4e3d2cf483cf0f2bbc6cf13bc42f0dbbf4efa3bcaeeb3b6aed33b0aebb3aceeb0bab6e9d3a68e89ba1ae7f39dee6bb990e583942e44b8bee1ab7bcde3375cdcfb70edc0b6d2da8b684d75b5b8d66b57cd57b540d48b4e0d2c346ed0b340ecfc33d2ced3372cd53336cc632facae3276c96323ac8731fec7831c2c693186c5a314ac4b310ec3c30c0c1fb03cc07b000bf8afc4be9af88bd1af04bb9aec8baaae8cb92ae08b7aadccb6bad90b5cad54b4dad18b0d2b62accab02ab4aab4aa5aa78a9b2a60a8c2a12a81a9e8a72a9bea682982a592958a4ea91ca3fa8e0a3528b6a26287aa12a81a9faa7cc9eba7909dca7549c927069ba26ca9ab268e99c2652991a628982a5ec973a5b0960255094ca51493da4ea93324ae9242460910a4248d923468cea24488e222c888221488221fc87c21e48762118843210083d20e883720be8282082819205880ea02e808a0168029ffe7fc9fe67f69fce7f09fb67ea9f9e7e49f867de9f6e7d89f447c99f087ba9ecc7a71e6c78f1e0c7771dac75f1d4c7471cec7339cb07249c747159c387069bfc6f79bc06e89b846d99b486ca9b0c6bb9ad06ac9a9469d9a5868e9a1c67f99e067099a4666198c6601974651192664218b46259878616983c60798005f897c45e517765d617285c296ec5b396b05a49674595963858215b45611566552152a53e94ca526947c517941c4ff93bc4e793804d else (if i < 5 then 0x3016106816103418142a06109e08103011400c5208a00684a0040c04040c03848a041807082807091408300e100c18161002070c1a06081806c1060d03608321e0820601b0418a00d820c8982081806081a06081806c0060d03600321e0020601b0018440d800c89800818060a160b101618384040a0b020a192c1000c182060c1c182060c1c183830515400896081440688080060b00160b00160b0016081c10344a085440688092d83802288c506860d0c1a1834306860d0c1a1824ac0054305880e04103020e041c08381070ac0808785c0848bc2d0102212c10000286081430686080c40685400a85400a85400a840d0816202c305860e141068301007030100602008001385301808038180602006178289ab0b830b0b830b0b830a810810a60050a604103a0430010a60050a6040c385302061d02180045501081c116062c0a2a80840e2c0a2a80830e2c0d02180045501081c08aa020c3812c0b00142c4e26003034bc5400527128a9341ac51c4a4d06b14710160aa4a228943a0d028e4a160312121f1500141c3e2818ac30988c10982082c14c98331186c260b1c9c202c007080e101c203400616c08506c085050a6040c385302061e101c2034007080a2e808a0f080e101a0038405174045068aa020c3c2038407080e101c1838307060d00160038307060d001c182c085050b60428385302081e0c1c1834007060d001c1828ba0228345501081e0c1a0038307060a2e808a0d154042078307040e081c1038207040e081c0820d0602410060281006020001f0260341208030140943010030287af09810b09810b09810a140d141450200144a085440404502c5040a1834306860814306860d0c1450203101a103420685400a85400a85400a840d081a10342058a0b1182131016182c305860d041a08341040a0834106820d041a08345a08545a0854106820a28101880b0c16182c26004c205840834100703010040100514a452281001a0c048200e0602810060200801146800000000000000c048200c050180801412994000000050c1a1834307000800a04000000000000000000000000002880d101a2038007000e0b00160b00160b00160b00160b00160b00160b00160b00160b00160b0016001c0038007000e001c0038007000e001c0038007000e001c0038007000e001c0038007000e001c0038007000e001c00380070008000005128215101a2024b60e008a23141a1834306860d0c1a183430686092b00150c16202c46084c305860d041a0834106820d041a08345a0844ba2e0082251682131016182c3068b430a8b430a8b430a2a0c54125600881c54125600861c5418a834406880e001a2024bc0128325600861d101a2034406860d0c1c0034307000d0c125e0094192b00440e860d0c1a25042a25042a250426282c46084c else 0x3412103016103011800c1807098a0b1016182c1043541068619048484041408681810600e10500e120c10d51418181686090c1a09081a0b0a14083412106412122810683024550c213c0c206820206822801a0e8010341010101a10)))
def layer507r9 : Packing := (559,3,6,63,0,14,1,packed507r9)
def keys507k10 (i : Nat) : Nat := (if i < 1 then 0x785390ee1cf34dc5b98096c6a14f34b2567f4328786cd8a014000906248d6618000d7ba42f00034e736aa5199877d3427105cc72a7970c635029a50a1a7a66fc7bf070cec489683685abd4101a094db7a4ddaa29352305240006599c7800025f70002515d4b344b3212568b33cc34f380000248800051840a2a03d985e622978c775179c32954746f90c8535a60f0002e2db79c000c63118f07e8000437fc0e90ff49012f4000b7bf439846d1ae54ab51ea77f5d9f10c0000367c80030f5a0c6bd06770b9c200003a0141098b4383b83e2709c2b0000000715907f350289964800000002887d8bb8c19849c5a14a4000f0191a20000a1663a901f05d697bf26345996849f2951b1ebe25b8fbd08c000f1cf0ef0001576f72f939e56dce2000313f22bc07c06d400000000ad529a4b84344000372310c304c000472890864bbd8aa18810407b115fd6ada08964d4642335590884e42780b7d7e0000c7215ffd32d19989c38a88418172c6573f5d07251699875ba93e811e05f804890b41c7cb767aa84f06e10f3f3d615e84be4c50002a21d43dc93d0124dbb73bc88f7524dc20cc000c4d51549893223d11b512a86bcdd13c9007e7eede0e55b605d66800050c405eb75b017809280b7747cfe46f255d76971c5206c000200dd0915b2cb1a7a1e2c94ed0ba860800090e8cbfb7e38a8105845b44b590054465649460000354aa27a28c000f1f808c706b5f003f0000267699552f81f38357e0900029830002528869ae260001028145288e000246e000190e000396f000344a00014ab000356374068eb03dd0c7b0e084907620a1000253045dc000b15e61cf1bc560d352855d80344c0000000b76d5c103e95f6e5650def2ec4aaa0b0103d02a60a93a559c21601021788876e3a0c0dc395222c6b55de26276179471c1ef150610f3b88cb62cc91a109b8c0127b01da477557369083d761c93dc7f01b3f1a420ce7d1d62b4911f932974b943b496d625646c479a07a1748d55147f42a7000000e4e19d0d5e895356c8000854740147b5d0565af074139149b0851d2613e3035b71f94b02b3a1ed6381b0c497c60a102c1141c301407fb0d086d89bb67c689163e44c400029cdd27dcb607030da0000c4de49d148b458d5ad38400096c49e50001ccc444c045377000075a50f1674c606804217d000255c0000000000287d0001cd30088703003120000003b620300000a6c1850004280260410300309000e04489003c2060409a9116b00000e313040c645890210307022c300000098c4000106222000b00000760008100002871202d898f000c883641c08010f4781004408612a000b020c02d0a143132638180101d4000200680b0004001e38017182878f220000d00001030e047a40c0010c0818001121c48d1a2c28002012043628da71401a013000007 else 0x134ad06e70d89708ad220c11000000000009810000165e58bb59c92b4087c8b72f28c9630a0f056d3572321800070dc8b0314555076a7d91518e53100010306142dc9c653c94c1dc000348440215621ba914800064e800000029fd000293395cdc6d481e0e6d29c015606688247186035604592a2261b7f5d19447603075780a0ae5594936412346b275cd1748a55ffc53008f0002e1985f1199586319ef025171f6a3143c82f61b953c45d252800067d45610338c9d1612ce3b31800040230f6968c0007283dd5220f085f6f5c7958a1910c4348ffb2d503ca22984eb844e15465adace5391e424294d7320709a13d0de3187e80cd24bdbfa83)
def packed507r10 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x7ff58541ffd51507ff5d531ffd744c7ff55131ffd724c7ff54931ffd424c7ff5c531ffd514c7ff50531ffe66487ff59121ffd63487ff50d21ffd61487ff50521ffd31487ff5da11ffe66847ff5ce11ffd63847ff5ca11ffd62847ff4ca11ffd515c3ff84570ffd75583ff5d160ffd54583ff5c960ffd52583ff50960ffd71583ff54560ffd41583ff48560ffe11583ff5d150ffd71543ff50550ffd52503ff54540ffd21503ff5d530ffd744c3ff55130ffd724c3ff54930ffd424c3ff5c530ffd514c3ff50530ffd214c3ff84530ffd41483ff84520ffd75443ff5d110ffd54443ff5c910ffd52443ff50910ffd71443ff54510ffd41443ff48510efc8199b7f9de66efd7699bbf99975bfe885977f9dd65efe66597df5d565f7d76957df99a55efe665d3df95574bfe885937f9dd64efe66593df95564bfe885537f9dd54bfd86553bf99954fbe66913ef59644f7e555cf7f9dd63f7e5558fef91163dfe7754fef91153dfe7750fdf95543fdd768cff75d633fdd658cff75d233fdd648cff755233efe665cbf78cd72efe6658bef91162fde3358bbf99952fbe4454bf78cd52efe6650bef59142fde3350bef91132fee6688bfb59622fed6488bfb55222fed6388bfb54e22fed4388bbf99971f7e555c7f78cd71bfe885877f9dd61efe66587bf59561f7e55587bf59161fbe44587f78cd61fee225877f9dc61bfd85187df95461bfd84187ef91061fee22186ffa2151dfe77546ff61951efe66547df59551f7d54547ef91151fde33547fb88951bfe885077f9dd41bfd86507bf99941bfd85507df95541fbd64507ef55141fde33507fb88941dfe774c7df95531fbe444c7fb88931efe66487ef91121fde33487fd21a11ff576847fd99a11ff575847fd59611ff574847fd59211ff554847fd5ce11ff563847fd54e11ff543847fd5ca11ff562847fd54a11ff542847fd4ca11dfe77847bf99a11f7e55847ef91211fde33847fb88a11ff571847fd58611ff551847fd50611ff531847fd48611f7e555c3fd84570dfe77583df95560fbe44583fb88960ff6115837f9dd50fbe44543fb88950ff6115437f9dd40f7e55503fb88940ff6115037f9dd30f7e554c3ef91130fee224c3fd84530fbe44483fd84520dfe77443df95510fbe44443fb88910ff611443fe5da00ff975803fe59600ff974803fe59200ff954803fe5ca00ff962803fe54a00ff942803fe5c600ff961803fe54600ff941803fe48600ffa118033f9de66d7e779579f99a55dbe77913af99a44f3e55913779de33ede668cfd795633f9e448cf7b9de22eee6688bdb95622fae4488bf38ce229fd87186df61461bbd84186f760c61bed82187bd58461bf9801877d9de11ef666847dd95611fb644847f58ce11fe6228477e9de00efa66803de95600fba44803f68ce00fea22803fc84600 else (if i < 2 then 0x98784ab034e1e16018c98985805d262e06247e1ab2840d1882c24142a1f30de2e186e08b050ad0398b8819822c142b40e62e20de085058751862e2c142a273618e62e20de08b0ad0398b883782141621460e24561e12be022d1810080ad8b8915878582ab5e0e2c561e129e022518b89158582a5808742b62e22861c560e021538b891587849f8083422e0cac76261e12bc0538b8987825f2a260cac762e1e129c0538a872b1d898582a5014e2e261e097cb8a832b1d8987849f014e14ae2a56261c760c0539c633656664cc2d96c329564ccc8dd90031dd633cc58d89c30f96194c23d83030295fecbf0d7ca2f655e7cbc1d76e2eb55d14b98d71e2e115bd4b70d6c22d595a6cb42d6702cb958f4b14d60e2bd5575cadad5a22b0955b4aa9d52e2a1553aca66d4b6292d51fca33d442284150349fcd3e427954ec49cdd38a26e14d5c99cd31c26014ba4962d2a8252549ec92ed23e2445480c8f3d1c8236946548bdd1602285448487fd0e4219142a4844d06a209540d480ed0021fcd3f2c7d7cf9c1f053dbc7a7cf301e353bfc775ced81d713a64740ce621c9538cc70bcdfa1bb9370c6d6cd901ae535646a6cd3c1a5d3494686ccfc19d13354662ccb419593274642cc7818c9313461ecc2e1839300c5f8cbda17952edc5d1cb9017092dd45b4cb5a169d2cf4595cb1c16152bcc574cada15992af4558caaa15352a2c540ca6e14b9293451dca2e1439283c4fdc9f013c927544e1c9b2132925f44b4c9501271247c483c8f811c12354462c8ba1155227c449c88210e12174422c832104120243f9c7e60fa91f1c3d9c79c0f1d1ddc3b1c7520e791cac38dc70c0df91bb436ec6cc0d751aac34ec68e0cf919ac331c6520c7d18c4313c6180c1117fc2f8c5ea0bb1172c2dbc5a40b2115f42b4c5560a89149c28bc50809f1139c26bc4ca096d128c247c47c08e5119c22bc44c087910c4210c416080d0fdc1f3c3d807910f041d8c3a407290e141bac36606ad0d2c19cc32806310c1c177c2e005a90b14159c2a2052509f4133c256048508bc112c212041107d40f1c1d0038906c40cec194030105dc0b6c15c029d04f4095c11a021903ec074c0d8018102bc04ec08a00f1019402cc0460065009c009c0003ff99975ffd76597ff99974ffd655d3ff59564ffe66553ff5d563ffd7458fff55163ffd7454fff99972ffd635cbff59162ffe6654bff59152ffd6354bff50d52ffe6650bff58d42ffe665c7ff59571ffd635c7ff54d71ffe88587ff61d61ffd76587ff61561ffd75587ff59561ffd84587ff5d161ffd64587ff55161ffd82587ff5c961ffd62587ff54961ffd42587ff5c561ffd72187ff5d951ffe66547ff5d151ffd64547ff5cd51ffd63547ff50d51ffd71547ff58551ffe66507ff59541ffd63507ff54d41ffd62507ff54941ffd3250 else 0xc140c04b4aa2d7130f0b090702142c2b48561600d29e2a2618b0ae08e5915130f0b070503012d2a8958561600d296221e08b0ae28dd915130f0b090503012d2a875c4c3c2c241c097ce3b15130b090705012d2a835954b450bcaca378b862c142a3b3c4cb4509caca3989822c142a553c3cb45094aca3b2d141f2b2c262e1e112e00e8e505517110d070500634000d2b62e1e10e2a8ed21713110d0b0705030127095858562ab61e12a8e0ed2140784a5818a363b445c4c44342c140c049a1c25717130d0b070301268509545c1c140188ecd0789858243805437445c2414017154c0034ad89858236aa55485c443c342c24140c04941d617858036543b345c443c342c140c0492241d617801588ad82aa365548560e129e00da21551170f0d0b09030124850750ec5c44342414017508b090703052d1d3c2a241c0cb41474f0b0887032d051d3c2c241a0c14b474f0907050127032f3c5c221c14049c0cbd1170906850103272f40524a38e2b0daace888480a48a9f34522a221a0ab2ace9e9688848082a439429a2a1a120a0220e5086b29f1a922a22120a0218dd0a4968a8684828088374a2212b2927a74c848090e1222a1a120ab0e274e8a888482ac369d3a9a0ac2948868480ae82a7320abaa46ae968482808aa637421a0abab29a74caf1709070503008b154ab42c241c140c02ac552a7170b0705030089154a945c2c24140c021c552a1170b0907030085154a7c5c2c241c14020c552968a88868480a49f424a423a322a221a120a00e0d85855c968a86848280393a5a2a22120a00dce8a88868482ac9d3a5a221a120a029abd11489012b25211f3c2404ac94847cd2b148b0907050301214cac542a241c140c048532b150b0887050301214cac542c241c120c0485305010d5f24541ca98c84b150a87032b09213c541ca98c84b0b0703012a39213c5424a97484b150a89032b07213c5424a97484b0b0903012a37213c522c241c0c14acf150a890703052b3c542c221c0c14acf150b090683052b3c048cac71487012f2b27213c1c04bcac9c84c8b090703012b213c2a241c0cac0484f0b0887032b01213c2c241a0c04ac84f0b090703012b213a5222917a7ca96948483009e88a542524a2a221a9e097d09694888500869f3a523a2a220a92197d09694908a8884a6a58300875a5a52120c029a94e9486ae5ea72a5a521a140222bce96948a8500ae86a7425a221a14022a927d0928e8a8886825f3a5a4a422a1a120a9c0225496908e8a888482a50087525a221a14020a9abd11c968a8886848300954e02bcb6261e160caa2d3878580632602b49e2e1e160aac2538985805d2602b62c9626160aac1d28983258b8580a707422e0cb486261e02bc1538b8987825f2a260cb4862e1e029c1538a872d21898380a5054e16018974980ad8b1f8)) else (if i < 4 then 0x8301049e892aa460cc705c52542222121c14043279b14950a8a8500a6a51c8705824f2b70c4705c52524c22241a1a122c14023c320289f1c1714950a8b0686848905008f0c81127c7452542a14022c121caa99b1c148b08888684510500a50c9e6a4c2a2a241a1a140a0c029c74112cade8f0a8b08888685028300a51d04432b7a7c70542a2a241a1a1144120c043299f1d0a8b08890686850282510500950c78cc7452541214221caa794491c148a87048508a52a9e5a3c2a2a1c12140a0a94710c24ada289f1d14950a8b048489068f2a6a4c2a2a2412140a0a9c712c1cada409f1c150a8a89048506832aa6688c52520a7a2414aa912231697149511088887050c9e62522c029a921e0c8cad223169714949311088906868b048f0c788a7c5a5c5254442a2c1a1a24123c31e229f14950a8a87052aa6508c5a5854422c22221a94143279a928a88868300a7232b4a3a2a221a0c02948cad2229f169615110a8a89068683050ca6788c5a5c442a2c22241a1c0a0c125431e910a8a870485011e432b2758f45a5c2a2c22241a1c1214043a5431e5b1c15048483009e892aa458cc7054222412121c027ca96a51c150a8b0485004e8782372a68c470524c22241a1c12122c023ca9c289f1c150a8b0687048489008f2a71127c70542c12122c021caa9991c8704848aa589012a9e529c742a2c1a1c12140a0a2400e4a9ca51d0a8b0889048502828700372a727c742a2a2412161a0c04aa998928e2c2a952abc54241c0a2cb4ad094882ca42a9f34240c958c8181380358b09872c392a3b5954541c1404b4a98d115130f0b07022d082b4cb05a082e14aa90e27d2950884808aa49f3c9a522a1a0c22b2ad107331f1c5c522414041c7ce1a0f80358907832c372a555c542414017154d15130f0b09022d062b4c542a24140c04b4ac929c1d707844f8036543b3c5c542414017154eac140184aa543a37405c5444342c2414049c960c1d924948a888306acab42522c1a120a02b2aa9c922571489052d251f1d3cb4522c241c0c04147532d150a89070301051d4cb4542c221c0c041475315072c631d2c542a1c0cb42474f15092c5d1d2c542a240cb41c74e9488a45e9f2a5a54120a027a2295094928a8886a7825f425a522412021a7ce948e8a8882a4865f425a52322a22029a94160a1d727033125245c52140c049c94f15072e2c2b2734521c14040cbc9cf15072e5f272c0ca4bc71714870501092f3c5c541a140424bcf0b03275d22b05c2e100aac98dcbd317150a85012f072744521c0cbcb49c74f1e948a888702acab42521a120188ecc3a94888480acaa5d425a52120170eccac948a88870280849d4a521ab18a74a9488ac5c9d2c241c1404942c7cf1689070501250b1f445c241a14042c947d01a18120f84818b8987832d14352b7154543c241 else (if i < 5 then 0x331f4a9c9452542a282608b0ac18d591495110d0a8b04850081272507824e97814c5254120c04b27a24729163217149508890087049f1c5c52542a2c14029a921cb6093c75a33149508872c9f1c40c452544c22241a1c121402042a5c39e301714951308890686810a850e9c7452542a2808b0aa18d49d4291f14950a8b06870485008108970e7a522a140a02b2aa1c7c3ca56291e1714950a8b06868108850e9c70a47c52542a2c221ab43a716451f14948b048500810b06972769147c52522a12042ab41a7499815088907048500810b24971f605852241c1214020490e47d6150b088906805285249d1e5930542c1a22b4927479238928f8b8987858380372d2a356cb4aa2e1e221e160278d540b0888a42c142a9e3448e4b4ae2a261e160e00d14890483012d2a38a4e34856282618b608e0a8d12372d2b8b88878583803450dc221c1404b4aaca7d2158b89822c86362a34493c3c2a2a1c12140204b2960caa20ddf2d2a88838b878580a63554120c04b4aa9ac29510a8b0686022c142aa634544c2c1c120c04b4aaa0e548b0483012d2a36a6dd48585422221c12140200e4b4aa2a927de17110c848280a714a548d05c44322c24121402012a927db13110d0a8b090687048502830081264a978c5c4434221c1402ca7d235110a8b0485028300804aaaa48726378434221402012a92b27d3130a8b09068685028281264aac9d744c2a2c240a0c992a721ab5716960a8704850080a508389e605a4c2a2c1a1c12140a0c0200dab49aac20e65110f0d0a8b08890704850283008124429788d4442a2a24121402010aaa9c9608e5f0f0a8b088906850282812442ac9d743c2a2c1c0a0c910a7222b563417110d0a8b0704848300809e42a77c5c44342c1c120c027a3aa570d0a8b068300809e42aca7585a3c2a2c222412140a0c0200e2b492ac18de4a72516970a8a09048502830080063836816854120a7cb222947123215088904872c9f1c4a90542a293a1cb608dc71430149308890687048b2c8f1c60a278542a2c1a1c1224b23c718449e150b048b2c86a71c521a2cb296241472790a70a8b06860502832c88391c62942a2c2220140a0cb218dc7191e150a8b090687048500810297277058542a2c2412140c02047a18dc9dd1e150a8b090686805285029d26691c78542a2c221c0ab27499616150a8b0906870485008036ad1eab03278c7c5a5c2a2c24121402021c08dc99d1f0a8b0884ad87029d26505c2224121402022a94527d70a8b08890687048502830080971571645a5c22241a1a140a0c02024c5241f0a8b088906870282805285149c68c45a5a4c22241a1c121402022c5239e9e170a8b0687048500808314a768fc5a5c2a2c22241a1a0c0202445239e90890485004b252b1f495c5a5c22241a1c12140a0c044a5431e511d149484 else 0x16c525412140c02047c225c95914940aa42c082a349f48cc52542224121402041a5c7989489068480acab)))
def layer507r10 : Packing := (329,2,6,63,0,15,1,packed507r10)
def keys507k11 (i : Nat) : Nat := 0x2114237e2b47e114e995c5b101bc2fe34e65476f486c3a2c9ba3e0088be66190c89f1ceea4c27b84518166e27a131c9cf2807e3002f380827e7816834c80c1ab368003dddf44000111ee74a8418c3bf88bd4c8c1b883a5c18cc937f4c410cd100004b362808524504518e6b6ba19a1b45a8acf5d9c31c21ac92ec741a725b512d404ca6a602c59563d10d227ed222ef4e504c6aec3ea8d0548ef3700489553bf3700009cc0013280000003c100000000000001ef833b73ec000000c1258c4da825893621af5e20000208828e7c72c0000003e4800000003dbca807400072b4000000965e41c60dafa0000000001aebc16a2a80004c00000001a4fe4f01f2044988f3000023fc00000061828d4e1d92b35c2ae5ca330f73fbb7bd4642aa510003266ce6f5dd157cad8e3d7cc8fc86d850f4b739757e30036faada04569b48659ed162423e3382cc500000797c8efc9c000a357b5dc7234160c6a5e23f612fa43ccb27a2b778e615d18750aa193b851cf729425e4fe18de63d91726592513623ac3425316ef10b83d2d424afb8b6b3c113633f45bc48d82a8799e6c5f49126646280014b9668e173bc292b8462957aa7d20000a4983399570ea60f9ba6478105148c8184393230006ab0000082a31000117a000c6ec2f8000c3d84a7a9c051ed95178356de4621e078003471cb4f4f050fd85b26845606d00aa44c14800043c4019595480000000000629913f414669f856d6ba691388b7296026469d8003a3bc20000109e0f002cd92ca0e21021308cc2a302d48cd24e93689526ef1d6c36c21e8d67eb445db0eec42d71eac8580c7470a1562b68f3726a21a089098819a051b691e75285000000926a4891120442a0c0408200140803400380084c107300811800e818000000050e08281440dd00140438002042a30420200020c088280c39a046850c6c0030a062510f0810216020c05a004c3bb060c11f006cc84020020e1e180a5
def packed507r11 (i : Nat) : Nat := 0x505805a2422a487d22a2c48704b159c58a02721401e109522848485022c32d049953960b146e242800c7d02838385022c42d0491537627162840607062c227009043770a0510b121e3a71408045890e0961d49c144e2c3825820ea4d8a8a4a2412c0c7522c50185009929c501805a1c22a5c9d22c51c870a0042f40b1414dc2805c193a4501865cb131d38b0a0c544850090fa4487150a045890e0962b5890e722c43704b0a2b50b122034109161c2804c6a5b45880e1a283890a0c024310da28145890e0961d40b08045438500997a45c48714e42370600aa850088549101f38a04022c48704a90a4e0a27161c12a108526c54525120950642915162438208ace280432e549909c5008b121c12a42883121c22f002cf000452d121c28256983161c2270024f16242824a0039cb45890c841800a88b121c21f000ce022c4870a08a814422b162431d040514293bb33127d20114d07d00ef84efae70e02d78cfcc72c04b7aad4a3c97a8b883c7b271a6ac62259850e4a04323b63482be2501e21660f807c001ff5dbff337fd75ffacbff5d3feb27fd54ffae7ff58ffea9ffd43ffae5ff58bfea97fd42ffa65ff5c7feb0ffc61ffaa3ff507fe98ffd21ffc23ff5c3feb07fd50ffa81ff4c3fe907fd10bfcefbf99bbf2afbe44fbc67fb88bfb08ffa00
def layer507r11 : Packing := (39,1,6,63,0,12,1,packed507r11)
def keys507k12 (i : Nat) : Nat := 0x619a281ccfe8400002c0f70008696400265f80000450de7e5322fd476c9ef548400382f324a00063a0645776ce72503c20d8c9a1700256f49507649141182001027000001
def packed507r12 (i : Nat) : Nat := 0x5103081026ff
def layer507r12 : Packing := (1,0,6,63,0,0,1,packed507r12)
def samples507 : Array (Bits × Bits) := #[(0x1804cc1d81580000fcc00003060d800009c0007fff1e40ec00060000cf30001fffff,0x8044c0d815942905cca15010204814298ca15142b0e406ca256512847328a4a9453),(0x20870061e860000ccf000004081248000e7fff80002073300007ffff33fffff98000,0x850020a860c03ccf060300000048c05a46038c060011306032301d115180f98c0a),(0x0,0x0),(0x441800861180000f0fffff98319c70000f80000000c79c3ffff80003c3c0001e0000,0x4080000118009b505404f88119c7011df808f011e42943408f8047bc3c026de013a),(0x180e030f81e00000ff0000060c1e07ffff000000000f81fc000000003fc00001fffff,0x80a030f01e02852fa0142a2040a05a8560142a2854f01f8144a0a253b805149528ac),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe07003f001ffffff00000007f01ff80000000000000ffe00000000003ffffffe00000,0x20500150013881fc00000fc7f01ff80378001bc0378ffe0001ec00f62eea07f0003f0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8003fffe00000000000007ffe0000000000000000fffffffffffffc000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8003fdf400716000038b077ee0007260039307260bd6acb9705cb80000e580072c0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000007fffffffffffffffffff00000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff775a8000000418000020c05ebd5b24380521c0438000000218010c00000860004300),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfaf7eaffec77e00afabf0000000007c0003e007c00000003e001f000000f80007c00)]
def cols507 : IndexTree ColumnInfo := (.fork 25 (.fork 12 (.fork 6 (.fork 3 (.leaf [(1,0,506,0,10),(8,0,499,0,10),(16,0,491,0,10)]) (.leaf [(32,0,475,0,10),(64,0,443,0,10),(256,0,251,0,10)])) (.fork 3 (.leaf [(0,1,362,144,9),(0,8,179,320,9),(0,16,362,129,9)]) (.leaf [(0,256,211,40,9),(2,0,505,0,9),(128,0,379,0,9)]))) (.fork 6 (.fork 3 (.leaf [(0,32,217,258,8),(0,64,433,10,8),(1,16,362,128,8)]) (.leaf [(8,256,211,32,8),(16,1,362,128,8),(17,0,490,0,8)])) (.fork 3 (.leaf [(32,256,211,8,8),(64,8,179,256,8),(72,0,435,0,8)]) (.leaf [(128,1,362,16,8),(128,16,362,1,8),(256,8,179,64,8),(264,0,243,0,8)])))) (.fork 12 (.fork 6 (.fork 3 (.leaf [(288,0,219,0,8),(0,128,360,19,7),(2,32,217,256,7)]) (.leaf [(2,64,433,8,7),(8,64,433,2,7),(9,0,498,0,7)])) (.fork 3 (.leaf [(24,0,483,0,7),(33,0,474,0,7),(34,0,473,0,7)]) (.leaf [(40,0,211,0,7),(48,0,459,0,7),(65,0,442,0,7)]))) (.fork 6 (.fork 3 (.leaf [(66,0,441,0,7),(80,0,427,0,7),(96,0,411,0,7)]) (.leaf [(129,0,362,0,7),(144,0,362,0,7),(256,32,217,2,7)])) (.fork 3 (.leaf [(257,0,250,0,7),(272,0,235,0,7),(320,0,179,0,7)]) (.leaf [(40,256,211,0,7),(129,16,362,0,7),(144,1,362,0,7),(320,8,179,0,7)])))))
def levels507 : Nat → Packing
  | 7 => layer507r7
  | 8 => layer507r8
  | 9 => layer507r9
  | 10 => layer507r10
  | 11 => layer507r11
  | 12 => layer507r12
  | _ => emptyPacking
def index507 : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 11 0 6 2 0 keys507k8
  | 9 => lookupWord 31 107 6 11 7 0 keys507k9
  | 10 => lookupWord 186 635 7 14 10 0 keys507k10
  | 11 => lookupWord 109 376 7 13 9 0 keys507k11
  | 12 => lookupWord 13 47 6 10 6 0 keys507k12
  | _ => fun _ => none
def g507 : Forest := ⟨507,12,fun j => samples507[j]?.getD (0,0),cols507,#[[]],levels507,index507,noFactory,noFactorySound 507⟩
def packed495r11 (i : Nat) : Nat := 0x1ff
def layer495r11 : Packing := (1,0,0,63,0,0,1,packed495r11)
def samples495 : Array (Bits × Bits) := #[(0x1804f2ccac00159800330000306c639ce70007fff32b2c00198002ccb0006000,0x80472ccad83b59b07b360f01024218c6360f307f32b2d86d9b0daccb61d6c3a),(0x2007000f300019e0003c0000409084e739fff800003c30001fffff0fc0007fff,0x50005308039e100bc2010000000a529201900800c30804a900f05c2012403),(0xc09800f000001e00003ffff98ce318f83e00000003cfc0001e0003f0ffff8000,0x4088005000153e002a9505588ce108f83e0a5052814fc02a5e054b50d0a98152),(0x104e00300c0001fffffc000060f03e0ffc00000003c0fffffe00003ff00000000,0x4a00000c00cbea819c003320503e0ffc0063031940d7418e0031bff006500ca),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe07003c00ffffe00000000007f003ff00000000003ff00000000003ffffffffff,0x205001400c42ac00055000aa77002f7000014a0a53eb00054800a90aa215642ac),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8003fff0000000000000007fffc0000000000003ffffffffffffc0000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8003ffa033300066600ccc5fafc000000d8c6c62bf28b67156ce0000d981b30),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000007ffffffffffffffffc00000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fa8000023c000478008f07efdbde52949f04f800000278004f000009e013c0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdba57ebaf3bc00157802af0000000000000e0070000000380007000000e001c00)]
def cols495 : IndexTree ColumnInfo := (.leaf [(1,0,494,0,11)])
def levels495 : Nat → Packing
  | 11 => layer495r11
  | _ => emptyPacking
def index495 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g495 : Forest := ⟨495,11,fun j => samples495[j]?.getD (0,0),cols495,#[[]],levels495,index495,noFactory,noFactorySound 495⟩
def packed503r7 (i : Nat) : Nat := 0x46b5b9aa96419211
def layer503r7 : Packing := (1,5,6,63,0,0,1,packed503r7)
def keys503k8 (i : Nat) : Nat := 0x0
def packed503r8 (i : Nat) : Nat := 0x2800800014002000050008000005000800500081800200000000100000000000000140020000014002000000000000000000000000000000022a8a227e02252fb3cde0ed72b89bedc6a3459ccb643017aba592bd4ea450a7936984aa491e8c44a1906803e9e8ee6f361a4cc632d960aa52279309246219007a3a1b8d0622e158a04a220f87000d5d9dc9161564aafaa96460464cafa656460464e1f2627799954c5f2627799954d8f2626659644f0f9de6659644d8f2a66655244bd52859559233f179de6655233f279de6691233bc72a56591233f479dd65912339d72a56591233f879995491233f1b9de6659622bd92859559222d9b2a666552229db2a66655222f8b9996591222f339de668ce22f539dd658ce22f93999548ce22fa399a448ce22fc3596448ce22badaa96419211f2d9de6691211f359de668ce11f659de448ce11fa599a448ce11f399de6688a11fa999a4488a11f719de3388a11fb199a3388a11fe19123388a11bdc2859559200f1e9de6655200f2e9de6691200bce2a56591200f4e9dd65912009de2a56591200f8e9995491200f569dd548ce00f669de448ce00fc6552448ce00f3a9de6688a00f5a9dd6588a00f9a9995488a00faa99a4488a00fca5964488a00f729de3388a00fd25523388a00fe29123388a00f3c9de6684600f6c9de4484600fac99a4484600f749de3384600fe49123384600f789de2284600fb899a2284600fe89122284600ff08ce22846008af6a29959064
def layer503r8 : Packing := (63,4,6,63,0,9,1,packed503r8)
def keys503k9 (i : Nat) : Nat := 0xc5ef30ea052bc4256ff47e8dc005b0c080177b0bb380000492001ec0000128733650005a801c8849ae52c59156104ca0a01e51f10999539d81bc25fcd6678033d40ad00fa00e000000000001a98001e2a996ea73bd18450f15b6efdf00044c004b4c90d0e0000028000839600501102c0110000002
def packed503r9 (i : Nat) : Nat := (if i < 1 then 0xf3bcccb0f3f9dd6458777d11222c3dbe7791161f5e4b488b0faf99a44587d7ac9222c3bde888cd61eef3bc66b0fb759233587f3c8919ac3bee8888961ef73bc44b0fbb99a22587ddac9112c3fae4488961fe719c44b0e7fa22775073fceec3283afe8899941e7f3bccca0faf25266507b7ceeb2283ebe6659141f5f33488a0ef7a2233507bbcef19a83bdd868cd41f6f33466a0fe759233507f3c8919a83bee8888941df6c3444a0fbb99a22507f5ac911283fce3388941edf3bc8898f7b9de224c7f5c8911263ede668cd21f7a4a4cd08f7d9de66847deaed33423ef6665d211bfb4cac908f7d9dd64847decccb2423fb49691211fdb3348908fbd99a44847f6ac922423df67758e11fdb222c708f7d9dd43847f6c88a1c23fd5768ce11feaba46708ff559233847fac8919c23ef6665ca11feb19ae508fbd99962847fac66b1423ef66650a11feb19a8508ff999a22847fcac911423fe56388a11ff2a1c4508f5f9dd54583b7cef222c1f3d5491160ef73bc44b07db55222583f5c89112c1df67784560fdb22422b07f988a11583becef08a81fb64484540ff311422a075f9dd544c3b7cef22261f3d5491130ef73bc44987db552224c3f5c8911261df67784530fdb22422987f988a114c3b7cef22221dee7788910fd722444887be99974803ef2caba4017fa9959200efd3bac9007de65564803ef2c8aa401efa6691200fbcb2c89007ee59244803fb2e919c01fda448ce00f7d332e5007de59572803fb466b9401efa6650a00fbcb2a85007f68cd42803fd2c911401efa665c600fed19ae3005fea6561803bf4eeb0c01ef96458600fdd222c3007fa88961802ff532a0c01dfa7750600bfccb283007be99941803f72c8a0c01fba4450600fed19a83007fa88941803df4cc90c01fda3348600ff8bb423007fc5d211803fe2c908c01ff24484600ff8b9423007fc58a11803fe28508c01c7e7799965bba48b0ab25afa656419357ac8c08c9a7c9899954e3f3bcccaa4df2626655397cef3348973c9859644e9f3bacb2278f999659126f930b2c89e3e6655244e6f3bccd19f579dd658cfabceeaa467e5e6655233ecf3bc8919fa799a448cfe3acb22467f1d5491233e773bccd1175b9dd6588bcdcccb2c45e6e6655222f5733489117cb5964488bb9cef19c45ece668ce22fa6b2c67117d35523388bf1c8919c45cf67799a11f5ab20c908f6d9de44847d6ccd22423dd6778ce11f6b3346708fe591233847bccef11423ee66688a11fd32244508ff18ce228479f4ef33401d7a7759600ebd3baa90079e99954803b74ef22401eba6691200f9cb2c89007ce55244803bb4ef19c01f59548ce00fcd224670077a9de22803dd4cd11401f696588a00fb4aa445007ea91222803f946711401df27784600f7933423007ec91211803fa46708c01fe22284600 else (if i < 2 then 0x2608545a00545a0054d06814d0896c1c01284a05342a05342a68340a68580200540a6844c60e009425001a05342a05342a1d002a1d0026282c561849460854d6004c305860b15861456298d8f29c5c971327c3e10649418aa2b148986e25285428130953652a9511b1a8b1b164f865546874a9328b81124d244d8d454d88aa54a6c755e124c9a20494d1389536391f02291d36231536251d36231702251f02251b362299499b1a8b81128a9b1154a94d8e454d8a45c08a44cd8945c088c7c088c6cd8944cd8945c08b818d88aa5429f00a5298b1b162b811636131e362e06362316362e06362316362c6c323e04523a6c462a6c4a3a6c462e044a3e044a366c45329336391f02291b36291f02231702251f02251b36231336231702251f022a6c2a3a6c5c0a6c4a3a6c54d870cd83cc125feafa17a6bc75d92e75710b735b5ed7f64db1ad89ac2f608acfd642af1569aa8d50aa55512a7d538a9954b2a4d520a8d5452a1d50ae83940d9ff4fbe7c13d19e14eaa72537a9b5cd4e6893359934c5e6112f096c4b02551290940c9ca491239910c8263f51d98e546ca3111708b0c52627511087c43821a30b9855424a0f5050817c082022ff97f0bf25f3ef907c0bda5ea2f27787bbdddbeec7757ba5dcfee79730b925c62e2270537c9bb4dcb6d9b66db18d866bbb57da8ed2f6903445a16cfc6723331968c9c64231d58bac45616b0557fabe55e6aed573ab8e5c42de56d4b5b5a62cf565cb1f5882c055e4ada5612aa9524a7a5312929476a2c50ea8393fe9e74ec27253749ab4c9a5ed2c694b499a46d2188f446522c913488b439a16d0868194051fc8fb47c23d51e6cf0676b3a99d10e6a71d37e1a70cd263630a97f4b825a92c415c0a9e51327913689844aa24911e88c444a21490447f23d81e00ea07203781b00d206603181800b3456a29d14709d84bc246117085840e1ef0eb86fc34e18f0bb857c27c12608703d81bc0c605702580fc06602b80fc04e00f0006ffa65811937fd10ba2c37fc9891161dff44488b0effa21725877fd10a12c37fc9899941dff444cca0effa2163506ffd32a0ac17fe9950530b7ec89093379f999655d27fb23442c99fe889dd64e7f3bcccb275f9dd85593afceeb2ac93fe9960464ebf3bcccaa79f99964552f7b2243489ebc9899a44edf3bccd2279f99965913d7cccb2489f3d6559244f9f332a92275f9dd5458fb7cef222c7f3d5491163f6f332e919fd7595748cefbd32b2467dde7759233faecaac919fd7591548cfdbccd22467f5d6591233fceb248919f9f999655cbdbccd19ae5f5d658cd72f3f332caa17b799a3350bebacb19a85dee7799a22bf74cac9117bb9996488bedb2ab2445f6d6559222fb7332a9117eb99a4488bbdceeb1c45f6d5458e22fd7222c7117f35923388bdbccd19ae39fe889dd61e7 else 0xb60f0030c8268681131bc008300b40d0040b81e8681103207a2a044c6f0020c0310340103008a120440c01b0841102206c11044e00383c284090401c0c050200c04190c7019a6202261604120434004180b048200e06028100602a6d7818433800b800a2d801502110504205d0420c30020ed042c16102c26082c16102a2d0c2a1d14220454229d04240434006810b06160838307060e0c1c2e0c2c2e0c2c2e0c2a0424089054105010b001a0c2c08689420a85440a89420924c10b0b800b1a0e00185d05810a131a0e031a1307801600160d01141e341c0634245b06808a13018d0b1a0e031a1600145b06808a13018d0b018d0b1a0c018016341c0634260f00286505810a1282c0850780071a0e031a15010016031a12318340450980071a0d010016031a12318340450980c68584c00584c00584c00583c0044c60858da004051686160081114e821504125b042c6b002c6d002608344a10544a105440406282c561845560858d600543068608143068b430a8b430b1ac008a4c10988c209880e13041613041613041613041613041613041613041613041613041608103040e081c1038207040e081c1038207040e081c16002c16002c16002a2d0c2a1d14220450229d04240434006810b0616082c56184c086860d0c1a18345a18545a18545a1845))
def layer503r9 : Packing := (259,3,6,63,0,13,1,packed503r9)
def keys503k10 (i : Nat) : Nat := 0x216158d90086071c4801a4597288fd01f8fad305b6b45940d82f5a681860dd21be1ff9fee36d3be958001a33b6432615ef0442070000526a6400033bc82aa3400073300000003469005164000936a1e8039821370a86ddb706800061890b4a0444040835ceeec97abb5840c827a47da5a80627547c12a3d6e86124e33d3dd2afd0668b98000ee375d2b500f2b01937800294985c429385f1824bbf23082f0d548716839f1507a86e4d99f492aa5d000792895de2f417129bc824c5640c8421b2e5163933f9caa00024400009564bfd2fa044000c230002ada9694a200038e5c3468c44fda2fc972b800000000002a7f0ebb455674c7d56ca94086822c01582245541e777027a12567ef6f1143852000478898c0012f97276339cf1207e482196ddb63c84249d80002ac03660a24198dc00000000012aae650bc000064776f80038f6c9d000313e46507387222d6891c4d60fe0c0000e31f48e19b162659d5053c8561c144750000d7c2a195eb34b026240b7b7badd2f8c427d9126c49c5335c8098425c2bb4a22a40dcecb444f8ec000000942c0145846d511f6c08da6c253715ba249905b170000047b06995e11c315ec3800001d119f88ab050026dafa5763388ea485c8250c39ad147c1604cdbf246b2f394700b419201946c39500040615c1c3c1408712e0082964400a02413800404000040818b3a2c781080030b00007840a444a5003159a1e0081e04e000006081000421382020c4001410089000400000007000200082
def packed503r10 (i : Nat) : Nat := (if i < 1 then 0x44f528ec09f13170e5239366cdab2f4ca3b220c70b16cc3db088c0aafe4bdfaf28ba6ae4cb7dad90b40acacb19ac08aecab5cabbaa90a88a9aca53a8d8a20a82c9efa7689c2a6c4999a610970a55493da488906a3ac8dda3308bea2cc89fa230874a18c853a0f882ca07c80f9ff87f09f747c99ee87aa9e5c7839dc07649d6474b9d0072c9c6c7099c006f09b846d39b206bc9aa46959a08670997c64b990062e987c60797c85e0972c5b1968058a95cc5619528530946c50993d04e2934c4c192c84a0924448391d0462913c43f90c042290444038fd83e88f5c3c98ef03a88e543818db835c8d443458ce032c8c7c30f8c002f68b9c2d98b302bc8aac29b8a4027c89ac259892823e88ac21b88281f487941d387101b886a419f863818285b415b854014084d412b847010a83fc0ed83780d483240b982b009a822407b81b805e814c04980e8028807400d8000ffe665d3ff99a44ffd7458fff91163ffe665cbff58d72ffe6650bff58d42ffe665c7ff58d71ffc84587ff5d161ffe44587ff5c961ffd42587ff21941ffe66507ff58d41ffd744c7ff91131ffd724c7ff50931ffe66487ff58d21ffd74583ff91160ffd72583ff50960ffd71583ff50560ffd21583ff5d130ffe444c3ff5c930ffd424c3ff5c530ffd414c3ff48530ffd74443ff91110ffd72443ff50910efc8499b7f9de66efd7699bdf5d965efe665d3df59574bfe885937f9dd64efe66593df61564f7d65592ff60464f7e66553df59154fbc86913ef99a44efe66913df59644fbd649137f9dd63f7d5458fef91163dfe7750fdf55143fbe4450ff75da33fdd748cff759233fde448cfbf99972f7d655cbf78cd72efe6658bdf59562fde3358bbf99942f7d6550bf78cd42fee6688bfb59222fed6388bfb50e22efe665c7f78cd71bfe885877f9dd61efe66587bf59161fbe44587f78cd61fee22586ffa2141dfe77506ff61941efe66507ef59141fbe44507f78cd41fee225077f9dd31fbe444c7fb88931efe66487f78cd21ff576847fd99a11ff574847fd59211ff464847fd91211ff573847fd58e11ff543847fd5ca11ff562847fd50a11ff532847fd84570dfe77583df55160fbe44583fb88960ff6115837f9dd40f7d54503ef91140fee22503fd84540dfe774c3df55130fbe444c3fb88930ff6114c3fd84520dfe77443ef91110fee22443fe5da00ff974803fe59200ffa44803fe5ca00ff962803fe50a00ff971803fe58600ff941803fe48600cfe7799b5f9dd65e7e66597af59064d7e775539f99954dbe77913af99a44f3d65913cf55244dde778cfb799a33f5d658cfd755233f9e448cf7b9de22eee6688bdb59622f6d5488beb91222fce3388b7d9de11ef666847ed91211fd633847f988a11dfa77803be99a00f7965803de55200fba44803f68ce00fea22803fc84600 else (if i < 2 then 0x5928d549d550b11504c4a34628415513c01254986e4d29150e4957015291c558a84825493c092a6095711524d364a74a44424113121b9e2e2916120e0a57023a953848382c595524d8ea46e2a16120e0a57023a98a8ec02295944e3849365458a138ec0129599293f008d4e54c4a4584434253c04fa529150d054d4b008e8904c4a428453c052a20f025e4a45582c454854d929e3229120a17024a78a9615c0149298565851364858a96c0239294722a16120e0a5b024a955858382c454964d92a6322a15120e0a5b024a98f4b4a458355c054a1291109055553008a84b4a4544834255c04ea5293b00895651c858482c0938d8fa231120a024e363e71b0907c4c2c5c395948d1cae2e1e120e0a5651170236a8b8583808d15141ca14c2f0f0b1454514a3472a1b0b8987858483829594c08db22e261e160f008e3688b89858482959443c08da870201b170f130a4e4a346eb8c88868482c0228da248140308724f130d52346eb1c0c8886858483829392c08db154330f0b104c4952346ea8c8482808d13121ba2321a160e0a4e49130236a8c88868482c0228da22d160e0256363a71b858483c0958d8ea22e150e0256363a71c848382c0968d92a231120a025a364a74442454f8d53992d150d015635527534c444342458d4fa115110d09554d514a3694155538ac054529d311109014e354a7444f4e8d555319552d150d0912353a84543444e8d559931110916354a6444243568d52993115110d095a354a843564e8d55521a0a423d36524c68b8a4584838294c090a54e120e0b165149364291b8a8584838294c090a62e2a16110e0a5302429948b858483824d90a22a43008a5251390124d9416284e43004a5268a90c0229496160e0a41365268b8a458384c0949d4e0f154a113652782c09194922e2a150e13025278b8583844d949a0a5a4136524868b458380948d909c6e160e0b0252364288b854380948d909d293f008d4e54c4a4544438253c04fa529150d054d4b008e88e4c4a448253c052a13129120917014a74a56c0235295312915110e095b014a94c448240534d4f9d2d251d150f008d3684c48454443535282c04da93112090159354a795c3cdc4569453c0a30a5711594e52367c5c315148d946f3454504f004a7c4c28d2291564f0f1711524a368cdc4c2c02295570e4f0b371711524b02a5593c2c5c492544da313084c49365c2cd56955390c09f37170f008e5c5c34d2393094f1656414936753c2cdc5529590c0a337130b008a555c5cdc454928fc0a30957124a3d51367c4c24d229337130b008a5c2cd9250558fc09f0f1309594e366c2c055c5c4c3548da317030d4f13094a368c2c5c355508d9b171309493e366c3cd5694538ec09f37170f008e5c5c34d23930d4f1652394936753c4cdc552948ec0a337170f008e5c4cd9 else 0x1c8a4a85844483824293c04c8fb46e292a151611120d0e090b01322ee1f8a4a458443829553c04f8e306e292a1516120d0e0a57012e3ad178a4a8444824285c04c92ac5e292911095617024938a1a8f8a4a45844483824285c04c92b86a3e292915120d0a1557024938d1c0584448242c0938d4c8f2d0a007d124e353a3c84947c5c4c3c2c095948d4b1c3116110e0a565301263596a0c898785458444834382421b9594c08d4bc6110e0a565302355d4a9458443829594c0478d62a9211b17130f0b024e4a35306cc0b888685458444834382421c9392c08d4cc615120d0a4e4b01223592a43802145958d4f8e206e1514120d0f0256352e38b178b4b498095458d478e293e160069150e56351e38a1c8f85458444824283c08d4c92363e15160d0a007d12353a48b1e8e8a4a454443828453c0944f346e3a292a1515120d0e0a13012e52e178e8a4a44828445c094522c693e3a292a15110e091613025148e8e44401e8482534d864f2916110e094d4b0219368ea4f8e85454443401e84824d865234462929150d4e1302513ca118a4a8545834384c04b94ac46292916130251488114f8a4a85434584c094522c46313221014e1136193ca4543825352c04d9194a4453e31322215150d0211361948d8e844443828021458d4f942c6e3a151611120d0e0b02352e50d178e8b4b4984448280458d4794353e3a1611120a0069150e351e50d415315c01452995a2e2a0d1657025284a154fc0145398553c52354c51c8a8584838293c08fa556160e0b11524d363e9c3009594cdc493c2921c1bae2a120a065653008a88a85838115141c9e53164b124f0f09346462a9383c59215144d19a300544c50493664393c55))
def layer503r10 : Packing := (184,2,6,63,0,14,1,packed503r10)
def keys503k11 (i : Nat) : Nat := 0xb9505b000b2ad06c42f29000f5342b9a51b0396241533000969000e23a2d90f68125c00000000016f290e39b1496ab76000000a7ef13bad461e1800079179c000000271444d5e130154a64325f2fb5855d9436a1b4ea0de4df75567e4c9631ae047fa3170e7279b134f9d0169b2ca7c3c3267a2309c82192779d0ec5017b560d40b8b032d1289777460adb6e8d01526b65f2b7a8cf1c321e1d319b7821b77368ef17d80f5ad3eb288abdac93131a151238665108557f46285024c6634513d66c67dd37e1070b455f4f66de8f23ad9967c7a0d03056e11535904d98b8aa02f77152e4b53b63694860c3203b513f00041f54ab887931b1eb4000887000b7f349b7a668000000283b894a452c922ca900000000000018649e99f31e801da8000000000da6459e051001af02e9b3d6eb9439a000684662c070003aa027000000c1f9a2c02033b031c060f041b01160141000c0003005003000310080004015849314b0300060043031d0a21012939210d1a3e4700001400a6040011
def packed503r11 (i : Nat) : Nat := 0x702822b362141f009d42e6c586560149c605073624227007d2700c58700ac2271094d286ed9a04a93805094e326c4844e0129c24d1e3a0152738b080a6c5865600ea4d84064e6c5243a015a864d89082c02539c0608acd8850b402550c0a0e6c4845a012a41cd2c3a0152538c01121131a3e716243c084562c48670a0db06080d022c3271211b2436c16022c32a3474e3004484586929c14d203e0142738b080a6c58652010a4d83044e6c52442014a85cd8b0c240293829a58840284a716022c3283484f0e6c484589c09e1159b1624329028890a29586506cf161c4270890d9e2c39a4e2422502885362c32a4204f166c484487c09e2c487086cb126c586507409fe3f90e97bab59e7cc8b802da57da633b25ac7e848f29c9b5c64ab814a25d44c7bcdc17a286430670970c00dc007fd76ffccdff5d3feb27fc64ffc89ff5cffeb1ffd43ffae5ff58bfea17fd32ffae3ff587fea0ffd31ffa43ff5c3feb07fd40ffa61ff483fe885fe77dfccddf597beaa7be44fbc67fb88bfb08ffa00
def layer503r11 : Packing := (33,1,6,63,0,11,1,packed503r11)
def keys503k12 (i : Nat) : Nat := 0x126067820073d843844842a0041e00000e000161c2f4d192000b8668004758ba5fb36b52530000007220073600295efdba006310200d23800000a8113e0080
def packed503r12 (i : Nat) : Nat := 0xd1440c2026ff
def layer503r12 : Packing := (1,0,6,63,0,0,1,packed503r12)
def samples503 : Array (Bits × Bits) := #[(0xc04cc0f30580000fcc0000306c1800009c0007fff1e4679800007600030001fffff,0x4044c07305942905cca15010240814298ca15142b0e42399452036514b28a4a9453),(0x108700303e60000ccf000004090248000e7fff800020799fffff9980003ffff98000,0x8500101660c03ccf060300000048c05a46038c0600088a8c078983019180f98c0a),(0x601800c3c000000f0fffff98ce0c70000f80000000c79e1e0000e1ffffc0001e0000,0x20080041400009b505404f88ce047011df808f011e429e1e0136a1a04dc026de013a),(0x0,0x0),(0x180e030fc0380000ff0000060f0307ffff000000000f81fe00000fe000000001fffff,0x80a030f80382852fa0142a2050105a8560142a2854f01dc028a4fc0a2905149528ac),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe03003f0003fffff00000007f003f80000000000000ffe0000000ffffffffffe00000,0x201001500008816400000b077003b80260001300260bd600002c05640b220590002c0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc003ffffc0000000000007fffc000000000000000ffffffffff0000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc003fefe8071f800038fc7fffc007378039bc7378fff77573f8001cfc0e7e0073f0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000007fffffffffffffffffff00000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7b5a8000000418000020c05eadaf24380521c0438000000043000010c00860004300),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddef7eabebf77e00afabf0000000007c0003e007c000000007c00001f000f80007c00)]
def cols503 : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(64,0,439,0,11),(0,64,437,2,10),(1,0,502,0,10),(4,0,499,0,10)]) (.fork 2 (.leaf [(16,0,487,0,10),(256,0,247,0,10)]) (.leaf [(0,1,358,144,9),(0,4,211,288,9),(0,16,358,129,9)]))) (.fork 5 (.fork 2 (.leaf [(0,256,211,36,9),(2,0,437,0,9)]) (.leaf [(32,0,471,0,9),(128,0,375,0,9),(2,64,437,0,9)])) (.fork 2 (.leaf [(1,16,358,128,8),(4,256,211,32,8)]) (.leaf [(16,1,358,128,8),(17,0,486,0,8),(32,4,211,256,8)])))) (.fork 9 (.fork 4 (.leaf [(32,256,211,4,8),(128,1,358,16,8),(128,16,358,1,8),(256,4,211,32,8)]) (.fork 2 (.leaf [(260,0,243,0,8),(0,32,145,262,7)]) (.leaf [(0,128,292,19,7),(36,0,211,0,7),(64,32,145,262,7)]))) (.fork 5 (.fork 2 (.leaf [(64,128,292,19,7),(96,0,407,0,7)]) (.leaf [(129,0,358,0,7),(144,0,358,0,7),(192,0,311,0,7)])) (.fork 2 (.leaf [(288,0,211,0,7),(36,256,211,0,7)]) (.leaf [(129,16,358,0,7),(144,1,358,0,7),(288,4,211,0,7)])))))
def levels503 : Nat → Packing
  | 7 => layer503r7
  | 8 => layer503r8
  | 9 => layer503r9
  | 10 => layer503r10
  | 11 => layer503r11
  | 12 => layer503r12
  | _ => emptyPacking
def index503 : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 4 0 0 keys503k8
  | 9 => lookupWord 21 79 7 10 6 0 keys503k9
  | 10 => lookupWord 86 293 7 13 9 0 keys503k10
  | 11 => lookupWord 61 211 8 12 8 0 keys503k11
  | 12 => lookupWord 11 47 3 10 6 0 keys503k12
  | _ => fun _ => none
def g503 : Forest := ⟨503,12,fun j => samples503[j]?.getD (0,0),cols503,#[[]],levels503,index503,noFactory,noFactorySound 503⟩
def packed447r11 (i : Nat) : Nat := 0x1ff
def layer447r11 : Packing := (1,0,0,63,0,0,1,packed447r11)
def samples447 : Array (Bits × Bits) := #[(0x985600000facc0066000063000004e73800ffe0c1d996003001ffffff,0x8856424005acc856642802100084c63190a216040d99644b224aaa913),(0x80e218002ccccf0007800008492400739cfff00132661f8003fff999800,0x80a218c0eccccf18378c1800092582d294b0760d12260b8c1960f999b0a),(0x1300000030f0f00007fffc318e38007c1f000001c387e1fffc001e1e000,0x11000008f050f00132a09c108e3822fc1f04608d4286a1a11c08de1e04a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc1c0460003f00fffff800033e0fc0007fe0000001fc07fe0000001fe0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc1404601ef500f543f801fb3e0fc06effe00de1bdfc07fe03d81edfe00fa),(0xe00780003fff0000000003c00fffff8000000001fff8000000001ffffff,0xa0078084bffa0010a00851400b6d0b0000214429fbf000089044955522c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0007ffffc0000000000003fff000000000000001ffffffffffffe000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd0004e21700000002c00163ef70004c0000098130ad595442e21700000b0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000003fffffffffffffffffe0000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5f50011800000023001182bde49270294a4e09c000000013009800004c0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000,0x2eafb1de00aaf0abc055e00000003800000700e000000001c00e00000700)]
def cols447 : IndexTree ColumnInfo := (.leaf [(8,0,439,0,11)])
def levels447 : Nat → Packing
  | 11 => layer447r11
  | _ => emptyPacking
def index447 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g447 : Forest := ⟨447,11,fun j => samples447[j]?.getD (0,0),cols447,#[[]],levels447,index447,noFactory,noFactorySound 447⟩
def packed511r8 (i : Nat) : Nat := 0x25a422a11f9e1c9b199816951392108f0d8c0a890786048301802c0fbb3554ef3330a42f41baee779998564885b03eecd55444ccba8eb493ddaaee7761485912947bb55dcccc290b226a4bb3277615a221644d517664ccc2b4442c89e82e77999856888591292ebb55dceec290b08d29d76abb9998521611d4b3664eec2b4442c23aa66cc9998568885847d0ccef3330ad110b08c6cd76ecc6148591211ad936eb0ad910b22423d92677615b221644847b44cccc2b6442c8908d25e76abb9dd8521600a53ced5773330a42c01a96acc9dd856888580354d5993330ad110b007a1a9de66615a2216008db8edd98c290b08c015b62dd615b221611803b2c4eec2b6442c23007698999856c88584600
def layer511r8 : Packing := (26,6,6,63,0,8,1,packed511r8)
def keys511k9 (i : Nat) : Nat := 0x28bb76c085200242520032800006c2d29e003841baa272628e80007bba40000002ce9d2b00417f3820a601030
def packed511r9 (i : Nat) : Nat := (if i < 1 then 0xc57dc66e6aa5d475e87eaaa22665d475f07e8899975644758b7dcaaed8521574ab6ecc615a221574ea6e66615a2215748b7dcaaed8521564ab6ecc615a221564e36cc9615a221564adadc2aaa7761644aeadc2aaa6661644d93ebb9dd8521644da3ebb9998521644f83e779998521644ec9e77999a321644ecae77999a221644eb2d76615a221644cdb6bb9dda121644ceb6bb999a121644ecb677999a121644f83e889de66956448b7dcaaed8521571ab6ecc615a221571e36cc9615a221571e36e99615a221571e96e77615a221571ea6e66615a221571db2d856c885911718b7dcaaed8521561ab6ecc615a221561e96e77615a221561db2d856c885911618f76cc2e97560551ce75c62e97560551c774baa657560551ce74ba9997560551af34ca5d644605518b7dcaaed8521541ab6ecc615a221541e36cc9615a221541ea6e66615a221541ade5c2aaa7761611aee5c2aaa6661611d976bb9dd8521611da76bb9998521611f876779998521611ecd677999a321611ece677999a221611eb64c7615a221611eb6677615a221611f87688999751d611f8758721e6695611f876889de6695611db65856c8855d211f8b6889de66912119fa5c2aed8591211dcb5b79988591211bb36cc6148591211f936776148591211fa36666148591211dd96776cc8591211de96666cc8591211dda6776c88591211dea6666c88591211f936889de5591211fa368899a5591211fc367799a55912118b7dcaaed8521570ab6ecc615a221570ea6e66615a221570db65856c885845708b7dcaaed8521560ab6ecc615a221560e36cc9615a2215608b7dcaaed8521510ab6ecc615a221510e36cc9615a221510ea6e66615a221510ade9c2aaa7761600aee9c2aaa6661600d97abb9dd8521600da7abb9998521600f87a779998521600ecda77999a321600ecea77999a221600eb6976615a221600cdf2bb9dda121600cef2bb999a121600ecf277999a121600f87a889de6695600db69856c8855c600db69856c885586009f70cb5d58154600f8f2889de66846009fe1c2aed8584600dcf1b79988584600bb72cc6148584600f972776148584600fa72666148584600ddd2776cc8584600ded2666cc8584600dde2776c88584600dee2666c88584600f972889de5584600fa728899a5584600fc727799a558460088fdcaaed8721e66a17dc9aaa7761485a27dc9aaa6661485d16ebb9dd8564885d26ebb9998564885f06e779998564885a17dc9aaa885d475a47dc9aaa665d4758b3dcaaed8521644ab2ecc615a221644e92e77615a221644ea2e66615a2216448b75caaed8521611ab66cc615a221611e96677615a221611ea6666615a221611db25856c885912118b79caaed8521600ab6acc615a221600e96a77615a221600ea6a66615a221600db61856c88584600 else 0xa080f141000d8a0c001ca040000b8a080a4010002400bc506003c203e101f080f8407c202000041040040f141000000f060f83040f06081e0c1f060f8307c183e0c1f060c1b060d8286c1436091b07c183e0c103c182001041001015004000003a202000041040001040000078207c103e081f040f8207c102078207c102078204002082002078a080000074307a1826681000020820000820000003005b4aff07e02561be0fc02411fc1f804823c28a43e0c7851487c18fe0e14888db17f83f018b4a46d8bfc1f80c5a5f19f07e0060922a150f19f064f19f062a47e33e0c548fe0fc00c11c542a1f063f831522f831522e99f046a47e33e0fc00c124542a1e33e0c9e33e0c548fc67c18a91f8cf8235238a089a89488387d86c86686084f84984383282c82682080f8097f87f27ec7db7ca7c47be7ad79c78b77a76976375d75775174b74573f73972872271c7167106ff6ee6e86d76d16c06af69e68d67c66b65a6496386276166055f45ee5dd5d75d15cb5c55bf5b95b35a259c59659058a57957356d56756155b55554f54954353d53753152b51a5094f84e74d64c54bf4ae49d49748648047a47446e46846245c44b44543f4394334224114003fa3f43ee3e83e23dc3d63d03ca3c43be3b83b236a34331c2f52ce2b22752382061d41ad18615f13811c1000d90a707504e027000c5fdb72dda1a6585a7edc22dda1a6585c6fcc6aeca95d581c6febb6d8a95d581a7edc2aaa9961571c1fdc66e6aa61c87b4edc2a667799985a37dc9aaa7761485a37dc9aa97661485e87eaa9de6661485b36dc12dd8564885f16ccb9dd8564885b36ccb9dd8564885d36ebb9dd8564885b36ccb5d98564885d36ebb5d98564885f16e775d98564885f26cb79998564885f26e779998564885e4f6aa9de6664485c57cc86e6aa5d475)
def layer511r9 : Packing := (149,5,6,63,0,12,1,packed511r9)
def keys511k10 (i : Nat) : Nat := 0x40852a0005bf000000743546d03c45e81589e97dae9a3e3a12f3c7800000684f868000000b080000200051c13383422738500000019993da8aaa58006b300e2a993c210449d006264a3283234c00d3ec17482d0fbb9d0c7c41bb00074973b8394c2c0798f03564a6b8bb589209683049fbafc13122a9a79bc93c32d8df2973e218fc71a843650b14273cb1dec1b15fa18ab40728bf1673adc8a895a8c253a0c9ef0eac633d22cc0d2b801b3c0a1f6ac09aea27a7e14fc3db70003abe92f981154c863242e5ad8909044bf94152162a8b7a4491e08a5c00088c5000120499000281a31a0618c8000006910246a6e24cb161cb94605b3680051d00002d6118000000a040850f06386801804e10000c4801c540801a01505209430070000170208c86425520d0d200004c01041
def packed511r10 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x21561803dbd444aab0c01f5e9de5558600d7f555442a3006dfaaa9dd518036fcd44eea8c01e7ea227754600ddf555332a3006ef9a899951803d7d444cca8c01f3e9de6654600def554baaa3007b7a885d551803f3d332eaa8c01edea225554600faf4ef2aaa3007e7a66955518037f955302a8c01f7c9dd8154600fde4ccc0aa3007f717560551803df85ad1108c01efca218784600fbe5113bc23007ef28899a11803f78c3ccd08c017fcaed8584600f7e510c2c23007df27761611803f793330b08c01f7c9dc8584600fde4cc42c23007bf2885d611803f79332eb08c01fdc2e25584600fee5112ac23007f718795611803df9444ab08c01f7c9de5584600fde4cd2ac23007f718595611803fb8bacab08c0163faed8721e66abdb654cceec2d6edb2a6666616a7f5db2f3310ba5faaa7761485d4fd553330a42f87e7799985217a6f3bcccc990bd3b9de6664885e6d96ec2b2442f36e77615922179b6bb30ac910b97daaa7764485cded553332242f4f677999912174bf55510ba8ebb1faaa665d475f0fd11332ea3af17e885d5911d7a3f332eac88ebe1f61c8799a55f0fd113bccd2aeb6d85688855d35b6c2b4442ac9e2fa227799a449f5b655530b226cbe776988591365ed3ccc42c896cfaed8521644f27ceec290b227a3e66614859136cf3bb4642c89ba7999a321644db5ceed110b226eae66688859127db5db4242c89b6d9dda121644dd6cccd090b22793e889de55913d1f444cd2ac89f0f9de6695644d6db0ad110ab8eb6d85688855867ba5d2eac0aa3adb615a221541f1eb0e43ccd08f8f6889de668467f2d9554c2c23b3d69e6621611b6ed76c290b08f9767761485847d3b3330a42c23bad999a421611dbaceed190b08eed66668c858476f33bb4442c23bb9999a221611dde4ccd010b08f976885d475847e3b332ea3ac23e5d61c8795611f2ed113bcab08fa768899a55847e3b3bccd2ac23e6da227791211f56d113348908fcb67799a44846edadb90b22423ecd6148591211bf2b6642c8908dfa5b221644847d9b444ab22423f4d9de5591211fc6ccd2ac8908eb6d85688855c35b6c2b4442ac1adb615a221510f1f5113bccd004fe9b2aa98580367d3bb4c42c01b3e69e6621600b6f576c290b00797a7761485803d3d3330a42c01b769dda321600ddb4ccd190b006dea77688858037753334442c013fcaeda121600dbe4eed090b006ef26668485803cbd444ef2ac01e9ea226695600f8f4ef334ab0079f2889de11803d79444cd08c01f3c9de6684600bbe36e42c23007b718521611802fe8d990b08c017f86c88584600f6e5112ac23007d727795611803f39334ab08c0107f6e6aa61c8786fb735530a42d36ebb615922178b73bb0ac910bc9b99985648858afb73552ea3aeb2d85688859135b2c2b4442c23ada615a221600 else 0x23f9d2a26695611fced11334ab08fe74a799a55847f3ac3ccd2ac23f9d21e6695611fcecef334ab08df75b521e55847cfb444ef2ac23ebda226695611f9ecef334ab08fd767761655847f3b3330b2ac23edda217595611fcecccbacab08faf68899984847f3b334aac2423ebda22665d211f6eb0a42ae908dfd5b321574846ff2d910aba423edda22555d211fceccd2aae908faf68899954847dbb444aaaa423f9d99a5555211f7696b4448908fbb68861e44847edb444ef22423fada226691211fd6b0f3348908dfb6bb61644847ddb4430b22423f6d9dd8591211fd6cccc2c8908fdb67721644847f5b3310b22423eeda217591211fd6cccbac8908ff34b895644847f9b444ab22423fcd61e5591211f76d112ac8908fdb67795644847f5b334ab22423fcd6165591211fe6aeb2ac8908c7febb2a565603d7b444cd08b01f9d99a55845809fdb655530ab85b7ebb614855c3d3f3330a42ae1bb7999a321570dddcccd110ab84ff6bb684855c377b3334242ae1e9fa226695570f5ed1133422b87b7585216115c2fead990b08ae17f96c88584570f6ed112ac22b87e7666956115c27f6d9554c2ac16dfaed8521560e6f972c290ab04ff6bb684855839be54d112aac11ffaeca961950f4fd11334aaa847febb2a58154337e54cccc0aa1ebda226684550f6ed112ac22a87e7666956115427f6d9554c2a21b3f69e6621510b6fd76c290a88737cb961485443d3f3330a42a21bb7999a321510dddcccd110a886ef666684854439be54d112aa21d9f2a66695510f4fd11334aa885bf9b129688803cfc5ad113bc01e7ea227761a00f5f16b444cd007afa8861e66803e7d444ef334013fe6c6aa61600dbf5553bb0b0079fa889dd858027fc5d2ecc2c01bbeaaa6661600f5f5113330b007cfa7799985803e7d3bccc42c01ede5d98521600dfb2ecd190b006fe976688858037f8dbb4242c01bfc6d9a121600dfe2ecd090b006dfa776848580377d3334242c013fe2e9865d600f5f511332eb004ff8ba61d65803cfd444eeb2c01f5e2a27795600faf5113bcab007d7a7761a55802fbc5d2ed2ac01edea217695600fcf151334ab007e7a8899a55803f3cc3ccd2ac01e7ea2277956009ff174bb4ab007afa8899a55803e7d3bccd2ac01f5e9dd8595600fcf4ccc2cab007b7a885d655803f3d332eb2ac01edea216595600faf4eeb2cab006dfaaa9dd81803cfd444eec0c01bbeaaa6660600f5f51133303007af98799981803e7d3bcccc0c01e7e9dd8560600f5f4ccc2b03004ff8ba5d581803ebd3bcaac0c01f9e99a5560600f5f511332e3007b798521571802fecd990ab8c017fa6c8855c600bfe36242ae3006f78ba95571803dbd444aab8c01f9e99a555c600f3f5113bac3005df9b721561803dbcc290ab0c017f66cc8558600bfd36442ac3005ff1b1) else (if i < 3 then 0xeeb2cab2274fe999de66607c7f444ef33303e3f9de66615818ffd7654aeac0e6fdb62a57560737e54cccbab03f1f9de66955818ffd7654aa8c0e6fca999954607adf4ccef22303e6fa227791181ed7d3333488c0fabe8899a44607d5ec3ccd22303f2f9de6691181f37ceec2c88c0fabe6661644606bde5caeb22303f4f9de5591181fc7ccd2ac88c0f2fe99a22665c7c7f444ef332e33fb6caaa61571b6fd76c290ab8f37cb9614855c79bf4cb0a42ae3e5f9dd8521571f4fcccc290ab8e7de9968c855c76ef3bb4642ae3bb7999a321571cfdd32d110ab8edee77688855c77773334442ae39fda65a121571dbeceed090ab8eef666684855c7c7f444ccbaae3cdf2a68895571e6fd33444aab8f97e8829e555c7cbf444ef2aae3d9f2a66695571ecfd33334aab8fa7e8899a555c7e3e53ccd2aae3f1f9de6695571f2fd10bacaab8fc7e665d6555c7d5f444cd222e3ecf6148591171bf3b6642c88b8dfadb2216445c6fdad890b222e3dcf2e65591171f67d112ac88b8fe3e66956445c67f6d9554c2ac36dfaed8521561f2fceec290ab0edde7768c855876f73bb4442ac3b7d9dda121561f2fd10ba8eab0f97d8721e55587cbf444ef2aac3e6fa227791161bb7b6e42c88b0fb3d8521644586fced990b222c37eb6c88591161bf6b6242c88b0fb3e8895644587e9f3bcab222c3c7fa658721d51cfed32d090ea8f1fe99a227754797f4cd11332a3cbfa219799951adfb7243ccca8f8fd8721e66546f3eda90f332a37bd6c48799951e9fd333bccca8f4fd989de66547c7f444ef332a3cdfa66885d551ecfd33332eaa8fa7e88999755479bf4432f2aaa37dd6c48795551f2fd113bcaaa8fa7e8899a55547b3ecbccd2aaa3f1f9de6695551e77d3344488a8f5be999de44547adecc4ef222a3e6fa227791151ed7d3333488a8f6bd9899a44547d5f444cd222a3f2f9de6691151ee7d32bac88a8fb3e885d644547f1f332eb222a3ecfa225591151fa7cef2ac88a8fe3e6695644547afb4cceec0aa3dbda666660551f9ecef33302a8f776995d581547f3b332eac0aa3deda664460551fb6cef22302a8feb66691181547f9abac88c0aa33fb6caaa61541d9fb4f3310aa0db7ebb614855079be5cb0a42a83e9f9998521541ddbcccd190aa0eeee666888550777b3334242a83cdf2a68895541ecf953334aaa0fa7e8899a555067fb5db4a43c23e7d2d6889de11f5e96f444cd08faf4b5a2266847d7b4430f334237bd6d48799a11f9ed113bccd08faf6889de668476fb554eec2c23e7da227761611dded553330b08faf68899985847e7b3bcccc2c23f3d9de6621611f6e96ec290b08fb7677614858477eb3bb4642c23bf99dda221611f5ed11332eb08eef5a899875847d7b444cc3ac23edda20a795611fae9513bcab08fd76889de55847dbb444ef2ac else 0x55877fb3bb4242ac37f76cc855d161bfdb6442ae8b0dff5b1215745873ff5d952b2b013ff6c6aa61570dfeb6cd090ab85fddb3215615c2ff6d910ab0ae17fd6c48558570cffd7654b0ca867febb2a5815423fed8d54ca90f37faeda526277b3fb6252d113bdafdb129e8899ad7edb94b444cd6bf6c4a5a22669dfd76d290f335cfdb52a27799bc7e5d5113bccde3f2d6889de66b9fb7052cef3378fe882967799bc7f4430f3bccd57f6c6999dd85afdb654cceec2c7febb2a576616bf6d9532bb30b8ff2a6885d985cbf9533baecc2d6fdb1a6666617a7f4ccef3330be3fa227799985b6fb6253b0a42f97cba9dd85216dbe5d4eec290badfaaa7761485b6f974bb30a42eb7eaa5d985217cbf3baecc290be9f29e6661485f4fcef3330a42f5de775d993217b6f3bcccc990bd7b9dd7664885eddcef3332442d7f6bb69d912173fb554eec890bd7d69e7764485ebeceed332242e7f6aa5d991217afad3aecc890bd7d9dd7664485edeb4f3332242f6f67799991217b7b33348c890bdbd999a064485e9fcef3332242c7febb2a5865d72fe54ceec32ebcbfa668899975f1fd113bcccbafc7ca8999751d797f444ccc88eb1ffaeca961d65abf972c3ceeb2eb7e8868497957cbe54d113bcabadf2a6885da55daf9533baed2af97e889dd76957d3f4412f334ab79f6c49799a55bcfb6243ccd2afc7cb99de66957e3e5c4ef334abf1f2627799a55f8fd113bccd2afa7e889de66957e3ec3cef334ab75f6d4a89de55c7f953442ed2ae5fca99dd76956f3eda90f334abe3fa227799a559ef974bb30b2afc7e7799985956f3edb150bacabadfaaa885d655f2fd113baeb2aee7eaa99975957d3f444ccbacabf1f9de665d655f2fd113bacb2ac7febb2a5656127f6d9554c2ae96dfaed8521574f4fcccc290aba6ede6668c855d37773334442ae93fdaeda121574ddecccd090aba7a7e8899a555d27f6d9554c2ac96dfaed8521564e6f972c290ab24ff6bb684855939be54d112aac91ffaeca961954f4fd11334aaaa5bbdb129688913cde5ad113bc89e6fa227761a44f5796b444cd227abe8861e66913e5f444ef334893ef6c6aa61644db7d553bb0b2279be889dd859127de5d2ecc2c89bafaaa6661644f57d113330b227cbe7799985913e5f3bccc42c89ecf5d98521644df3aecd190b226fad76688859137dadbb4242c89bed6d9a121644df6aecd090b226dbe776848591375f3334242c893ef2e9865d644f57d11332eb224fbcba61d65913cdf444eeb2c89f4f2a27795644fa7d113bcab227d3e7761a55912f9e5d2ed2ac89ecfa217695644fc7951334ab227e3e8899a55913f1ec3ccd2ac89e6fa2277956449f7974bb4ab227abe8899a55913e5f3bccd2ac89f4f9dd8595644fc7cccc2cab227b3e885d655913f1f332eb2ac89ecfa216595644fa7c)) else (if i < 6 then (if i < 5 then 0x864018f863c18ed63a98e2637d8d7633d8cc63118bc62a98a26269892622988261e987761d1867617d857613d847611183760d182c60918216065816603980b60218005fe17f55fc97ef5fb17e45f857d45e6976f5d8975a5c6d70e5c197035bed6f85bad6e35b596c95af16b45ab16a45a856625969657593d64c5911614583160457515cc571158055cd5665565556553954b552154554f553554c952f549d51f545d50f541d4ff53c94ef539d4df52d14ac529149c525148751fd47751bd467517d457513d44750e943250a9422505540d50154024fe93f24f953d84f413c84f013b84ec13a34e813934e4138d4e293874dfd3774dbd3674d7d3574d3d3474cfd3324c953224c7d31c4c5130c4bfd2f74bbd2e74b692cd4b1529f4a5d28f4a3128449f1274499d26449852594945249490523948d923348c122d48a9222487d217483d1f847c11ed47951dd47691d747511cc47111c146f91b646cd1ab46a11a0467519a465d1944645189460517e45ed17845c1163456d14e4505134449d11f4471119444510e442d10844010fd43d50ed43950d343050b942c50a9429909e426d098425508d4229055414904a407d017403d0023fd4fe83f6cfce3f04fb93eb0f9f3e48f853d54f4d3d28f423cfcf0a3c1cec83aeceb33ac0ead3a1ce7f39dce7439b0e643970e4f3930e493904e3e38d8e2e3898e233880e183854e0d3814e0237e8df23780dd83740dc83700db836c0dad36a8d9d3654d8d3614d7d35e8d6d35a8d623568d57353cd4c3510d4134f8d3634b8d2b34a0d253488d1a345cd0f3430cff33dccea3374cd03320cc032e0cb032a0ca0324cc903220c8031e0c7031a0c603160c4b310cc3b30ccc2b308cc1b304cc0b300cbfb2fccbe62f64bd62f4cbd02f20bbb2eb8ba62e78b9b2e60b952e34b8a2e08b7a2dc8b602d38b462cf8b362cccb2b2ca0b252c88b1a2c5caf62b90ad22ab0a9529f8a6c2968a48289ca0127809c926c899b25fc963253092b24148e923708c0229089221ec85a20e481d20187ef1f607c11ea87931ddc75b1cfc72d1c6c7091b506b81a7067b197c652190062418345fb17a45c816d85a41648580157c543149c50b13f84f113904d213004ae1234476117c44810d842410483f60f683b90e9c3900dbc34e0cc831b0c102ed0b582bf0aa028c09c02540908230087820c07e81e8071c1b0066418205c015e053012604140e402e409801c804c009800067fdb7686996173fe5bb434cb0b9ff6d1a1a6585cffb60d0d32c2d7fdb1a66776173ff5d952bb30b3ffaeca95d985efeceed332242e7febb2a5865d67ff5d952c32eb9ffaeca961d65cffd7654acac24ffdb1aa9855d37fadb34242ae99ffaeca961954cffd7654aeac0e7febb2a5546073ff55532c2ae33ffaeda521d61dfbceed190ab0efee776888 else 0x3a1c3c008a16860e860e860e860a800e860e860a800e860e860c860c95218525486100001248325c9214972484cd426582000032c0c1600360436042654a548c662c8748c74b034b026482032c080000e00200c12bf83e00b72b4c487824fc6487824fc64e9364d51744f83e00fe0a21e061327828878184c9e0f8184c784f818c47e0e178a46e43af0a782483ad3520e2b86ebf830a3ad3b88e138b0a782e94d85f83e06132617e0f8184c985f83e0613262fe0f808de2d2e2fe0f808de2d2e2fe0f818b4910f830bc2de04373443107830bc2de043739406bf83e01ad2f83e045c27822a70fd44bcb8a9e0f19c94bc6783e04628719e08bf271925c93e0f81290c8ef18a5a93e0f813719e08a1e04932f19e0f8124c9c6783e0493271924f812c49c6493e04b12719e0c972a49c678325ca9271925f83e04932f1925f83e04932f1925f83e04932f19e0f811f19e0f811f19e0f811a21c2f09c172fcb725e08a9c1d5c18a9e0f11caca10841e0f800dcbc2f07e08a9c672f31366bf83e01ad2f83e044287822fc68da96a4f83e04be08a1e04932783e04931f83e04931caf25c93e0f81288d24f812c4724f812c47e0c972a47e0c972a472b49724f83e04a634372bf83e04ad2c372bf83e04ad29366bf83e01ad2f83e045e0f811783e045a6783e047a6783e047a6783e0464de9865993e0f813699e0f8064c9a6193e01b12699e09966a49a6783e047a6783e047a6783e047c17822a70dd3cbcb0a9e0f19c94bc2f07e08a9c672d3719e0f8118a1c67822fc9c649724f83e04a43235c6296a4f83e04dc67822878124cbc6783e04932719e0f8124c9c6493e04b1271924f812c49c678325ca92719e0c972a49c6497e0f8124cbc6497e0f8124cbc6497e0f8124cbc6783e047c6783e047c6783e047c6783e047c6783e047c6783e0464d71865993e0f813719e0f8064c9c6193e01b12719e09966a49c6783e047c6783e047c6783e047e28400da2fe0f808b4fe2f87e6783e0041378be19210a799e0ccebf8b48786eb799e0c2947874838be67830a4c9078a0da2fe0f808b4fcbf8aa8787e08a9c64fe2f06a8725e67822a4fcb78aa8787e08a9c64ff2b7ca1f207c61f0b7c21efb7ba5edc7b51ed17b39ebc7aa9ea77a55e8879ede6e7971e4a78cde21783ddf877d5de37745dbf76b5d96764dd867509d3a74ddd3474c5d2e7499d23746dd137441d087401cf87321c8e71a1c607161c507135c457109c3a70ddc3470c5c297099c1e706dc13702dc036fedbd06f21bc06ee1bb06e3db876dfdb776dbdb676d91b2a6c75b1a6c5db0f6c31ad26b29ac76afdabc6ae5ab66ab9aab6aa1aa06a61a906a35a8a6a1da8469f1a7469c5a6e6999a5e6959a53692da486915a3d68e9a0567699d267299bd66c19a3665998965659516539946650d90e642d9) else (if i < 7 then 0x36003a00307000c06543041058b0c0884303800d800a810c810e166418e63783e04426790e003600362836282109ae6b78362d9033800a420d800d880d84080058140480e0300a02005e0f81291684580140021e0c0058140480e0300a02005e0f814917a00203120800014482000c4826502c48200000160036002001c003a003c00204120800212080078140380c02805c2783e04a4509b85e13c2f07c0f19c391c243c243c17081705c245c17081705c205c2704109b85f1584f07c1703c470e4f090c1c202001e0500e0300a01709e0f8129140006583a0826582001c00306800f000c1a003a042a548b89c6e2c2e282e2c2cb82e282e28200024700162e0f000e8a0a9208162d821016282a482032e081c00200160036002000001c18206138184050120400e030080100be0f810dd7abeade278510781e0c37400a8dc5c18207814048100380c02805e0f81a2706620f6005c1820706080c530617060d13418544d0611104dc5c183c183c182002185e13c2f09c10b3cbf2dc909be0d9c1c307070c1c1c20749724b10c3b0de0706c792e003c18206c9724b10c3b0de0f06c7d26043c1c305314c430ec330ac2106c1497e0f81249b04b801381050584e06101c18200007060f0608005060d060f060f070f060f070e80450407060f06089b85f1584f09c1783c411c1c3c1c3c183c1c2e040a17060f060f060f060f060f070f060f070e804285c183c183c18304b8017060f06081a003c183a010616804485c182c003c183818381838560610004e8010000007060f060b000f060f060b000f060f060d060d154185455061000018483848385e1214370c370e120e17848585e121237089b85e13c2f03c672e3f060f070c1c1c3c183c1c2e040810007060f00099609960996080000041a00306800e810aaf22e06ab48284307000d010c00412482a482000a48202920c062c200000005800d80080001a203a268416890e85a205a16891689a105a268416880800196080000ab8305800d810d81099529d25198b41ca71cae0cae0992080ab820000380080078140380c02809c1783e04a4501c10226e1784f0bc1f03c670c47050f050f09c105c27051709c105c27041709c105c270417050f09c105c27051709c105c2704109b85f1584f09c1f03c470c4f050c1c102001e0500e0300a02705e0f812914001e050120400e0300a02783e0687c118835801704080009b85e13c2f03c672c3f040f050c1c143c103c142e040410007040806583a0826582001c00306800f000c1a003a042a548b88c6e2c2e282e2c2cb02e282e28200024700162c0f000e8a0a9208162d821016282a482032c081c00200160036002000001a1820686080a528616860c93218524c8610904d45a183a183a183a1c3a183a1c3c0094101a183a183a183a183a1c3a18 else 0x1040e202e1020781410004780119e6418a1c90a28404020001300fc106d330fc1060294e2c371c8ea2041281f10100a84c7b10c286c7b10c286c7b1102b0a262b83e841e2b83e841a2b8390ba1080048037081b48c37081e2b837081e2b837081a2b8308bc208050cc1040c8160400e0300a0218601015e0f80049be002000001c0020294099608125022503a00246e1784e8ba2687a1683a512058140480e0300a02005e0f81291646e1784e89a1783a90f600)))
def layer511r10 : Packing := (639,4,6,63,0,14,1,packed511r10)
def keys511k11 (i : Nat) : Nat := (if i < 1 then 0x7617069e61df81c70a8a42cdc3112006146c8528f04d50fb6980810030c7998a2273f8804b06889e42c9d19a720a863ce6405aae910e2c88474f9b6239bb957c4fe619798990d71b59599cda88431ae27f6907b318d16396547600468fb20be8c7c904480c555c8e454b1e3a3249e4a2a940be2dc447c79763329b31bd74301d370609b7e363632d3c8e61d25644d3037cf7f9371b9c03f466032142b61f249b48fb82d2873cb6149e9b814b05d2f86dc29844bd44305fd210002d065132c0e196c4e7c9dd161372400090e342c63cde4a0388063701800019db09c81cc024071e267690c05f05d9a62f4934d6510262ef92ee1e16945d6f6c6909018251c72449229595db461fb931693e11495a654ea50dd534480186527a54c055f899f553df2b6859a3b2c72246811d8bf9738324523672723703ac1dc257d71308c07efcba47848974275c82e59346c94608c545bd98ac0f3d40883652eb5e0000c1b706213fdc19a48c000000244e000103dc014000000000065ea4e900000001746e37000220ef1e0000f2d4000835000000000001438cc10002e1632ad5dde437d41d4e1409f3d80000002d8197e5cdd0001c27a7c30bd56fb9d9000088fb9a116700000000002d7c0000000c404000a6b0000a06d10000000003083050e4f11cdd21bd5963f3a78c0534d151578496920000f7b7d2651bd57209f9a0544a8000000017420740001681983000327500016394148000c2280000000000c9380000000638e8d8000000000000000000000a31e72c00084d35c0b2b4000082d533f3b0c67d34911fe518000000116b224d4b2f7b8000533b962b83ea340000254a8d5dc50001dea43ac00085f6d77c9e8247981800014f40000001cb326f00a9404b0dca940d35475295ce022e0260c38cad21f9f822e3d5ad27de6a461c1e655600a4a99489a973c607982b53294fa0cf23995ab54b595dc983e00085499ae55aa5e37048f148855da27fd8bfd547439a7ad515c414cbe27b21dba300c7fd112d6ae1654dec77093a029cc3f82240d02676c9447c44ae76d9dfa09bf9ce86b4e7c5645d7f157aa6bc9338e12006deff632173058350a33ab16cc1d1e17a298ca52357229a11824539450a187f159b00000052020f042036030e050112004321752545040100090606011d190000000102071f0026010172040c0202421e080b002703160401005600060200007d0008091a1e0501320000011704001458381c0f00130a2113360a13a50e000f0100000a090a06280a00020100783a03000407010e05040002140801033f521f350201110e15021b0005430f0614410f0000323d35802201021000320200080605050d1b191b140c0700371904000c00001d000210962a4f13110300052026194f3e000e02001301042a090d330d0f01090d0033450400 else 0xc109e2768ae9a9d514d25872261d60dda2f665ea12c670256c21642622f02663918c6424bf91b48efc43680542ea20e4924763c3b10cf007c8b55cab50a85e07a1111f67cc10b65087bc46681a38e801fa409c3e58c18f4444d61840d0854f05a4fdc13c402f000d9576a044bd961425a105ce3296b5f3c160d50b830d79552a67062b3c56d63922ae33261a71c219278f75a2b35e823898e00ae28a8efb6c197e44af8bbe3ba82836cc87d075c0c2497d5d086fe98df144198665be3fa4e4104d071caf277a46ba393dccd383c15d08541e021398231ea890934ccb42468d478088193b850ce871c844a714fe264283e0854425c223970df297400031a3168e80c9030002508a15f8f55116a7bc94fd9e1612436e168213b4dfde722e6a1f1262004d948000e4fcd85000367df88c000158e13656012490000431f22c000a1751d5800d26e0001496d9c74cb000000057ddda4c52c00075ba219336c000447800000005af00000000000000000008861a40000000000353e549b8960f0816c4d9571b97ba5d713b7824df557f8000f9a6c5c828ca6d931000007d30ed256d255953412967a786a4335640a5c7130a666de016e846e245e5f6a3e14faf5b6264d78898f81d58c394)
def packed511r11 (i : Nat) : Nat := (if i < 6 then (if i < 3 then (if i < 1 then 0x7f748795611fdd9de55847bf68895611f7d9de55847ef66695611fdd61655847f757595611efda2184847ef66661211fdd95584847bf6885d211fbd99974847f76555d211efda2154847ef66655211fdd95554847fb68891211fed61e44847fb58591211fed21644847fb57591211fed95644847afe88999809ff2a565603e7e6695580efda2211603ef66684580fdd95611603afe8899970bbf698855c3b7d8521570bf768c855c2feda221570bfd684855c3b7e8895570f9f99a555c3bf68884570fbd99a115c3f765584570b7f69c85583b7d8521560bf768c85582feda221560bfd6848558377ca995560edfa22555827fca961950ebfa2266543b7e8895550f9f99a555427fca960550efda2211543ef66684550fdd95611543afe8899910b7f69c85443b7d8521510bf768c85442feda221510bfd6848544377ca995510edfa2255443e7e6695510efe29688803bfa8861e00f7ea2277803bfa8861a00f7e9dd86803bfa885da00fbea2266803ef98799a00bfeaa985803bfa8861600f7e9dd85803efa6661600f7e9dc85803efa6621600bfe68485803bfa885d600fbe99975803bfa8859600f7e9dd65803f78a895600fdea2255803f798795600fde61a55803f797695600efea2255803dfa7795600fbe99a55803f798595600fde5d655803f796595600bfeaa981803bfa8860600efe61d81803dfa7760600fbe99981803bf98560600fde95581803bfa885c600fbe99971803f7a555c600efea2161803dfa7758600fde95561802ffaaa54600bfe6a151803bfa8854600f7e9dd51803efa6654600fde5d551803f7a5554600ffc60551803ff28884600ffc61e11803ff18584600ffc21611803ff17584600ffc956118029feaa61c87e3f61c8799b8fe889de669fb68a996165feaa65c85d3f9dd962174fd9799885adfaa98521797e7761485e9f999852176be6665085d779dd932176de6664c85d7b9dd922176ee66648859fdaa9912175f67764485dbd999912176fa6664085b5faa9751d797e885d475f1f999751d757d7564475e5f61c87956e7da621e55e5fa2277957a7e8899a55f1f9de669579be889de44eafa2266913cbe7799a44b6f69c85912ebda621644ecf61485912f9da321644beb68885912fb5a121644ecfa2255913d3e7795644f8f99a559139f58721e11e7da2277847af68899a11f3d9de66846df5a721611edd61485846fb5a421611bf568c85846fe5a221611bfc68085847d75751d611edda2255847d767795611f9d99a55847bb68891211f6d9de44847eb66691211fcd956448479fa889de00ebea2266803cfa7799a00b7e69c85802ef9a621600ede61485802fd9a321600bfa68885802ff1a121600edea2255803d7a7795600f9e99a55803bf28884600f7c9de11803ef26684600fdc9561180336d8564885 else (if i < 2 then 0x5f9f26266957e7e8899a55f9f25e66957e7d8799a55f9f21e66957e7e7799a55bbf69887956f7da521e55e7fa22779567fca95da55ebfa2266957cfe7799a55f5f9dd85957e7e6661655bdfaa975957b7e885d655f5f9dd75957e7e665d655edfa2165957d7e7759655ebfa22666127fca959584f9f99a55613afe8899974bbf698855d3b7d8521574bf768c855d2feda221574bfd684855d3b7e8895574f9f99a555d2dfda721564edf61485592fdda321564bfb68885592ff5a121564ddf2a655593b7e88955649ff2a586553afe8899954edfa2255553e7e6695554eef29688913bbe8861e44f6fa2277913bbe8861a44f6f9dd86913bbe885da44fafa2266913ebd8799a44befaa985913bbe8861644f6f9dd85913ebe6661644f6f9dc85913ebe6621644bef68485913bbe885d644faf99975913bbe8859644f6f9dd65913f3ca895644fcfa2255913f3d8795644fcf61a55913f3d7695644eefa2255913dbe7795644faf99a55913f3d8595644fcf5d655913f3d6595644d7fa66776079fe889dd81dbfa6666607afe8899981ebf61e66607cfe7799981e7f9dd85607afe66615819ff2a575607d7e7795581f9f99a556067fca955181defa6644607bbe8891181eef61e44607dbe7791181faf99a44607bbd8591181fcf956446073fe99a2171e7fa22775c76fe9999971dbf662665c7afe8899971f3f9de665c7b7d8521571bf768c855c6feda221571bfd684855c79fe885d571f3f999755c777ca995571ddfa66555c7b7e8895571f5f29e555c7d7e7795571f9f99a555c7d7d7595571eefa22445c7ebe6691171fcf956445c79fd8721d61e7fa2277586dfda721561edf61485586fbda421561bf768c85586feda221561bfd68485586ff9a021561f5f5d475587b7e8895561f5f9de55587bbe8891161f6f9de44587f3e5591161cffa66885473fe8865d519ff6a4875479fd8721d51bdf69487546ff5a121d51d7fa66775475fd989dd51e7fa22775476fe9999951dbf66266547afe8899951dbf65e66547cfe7799951ddfa6575547b7e885d551f9f99975547b7e8895551ddf65e55547d7e7795551f9f99a555477be9991151def66244547bbe8891151f6f9de44547ebe6691151fcf5d644547f3e5591151dfda6581547df67760551fbd99981547f757560551fed91181547afe8899941b7f69c85507b7d8521541bf768c85506feda221541bfd6848550777ca995541edfa2255507e7e6695541efd29e88847bf4a5a2211efda2187846ff5a521e11f7da2277847bf6889de11fbda2266847ef58799a11fbd21e66847ef67799a11bfdaa985847bf68861611f7d9dd85847ef66661611f7d9dc85847ef66621611efda2175847ef6665d611bfd6a075847bf6881d611fbd99875847f74a895611fdda2255847f74a795611fdd61e5584 else 0x7bfe8861541fbf99985507efe6621541fdf2a255507f7e8895541effa2255507efe6695541fdf61655507ff6889de11ffd29d85847ff67761611ffd9dc85847ff6885d611ffd61575847ff48795611ffd9de55847ff6885d211ffd61574847ff4855d211ffd95574847ff68855211ffd61554847bfe8858580fdf95561602ffeaa54580fbf99951603bfca5a2170effa21865c3efe8899970bffaa9855c3bfe8861570fbf999855c3efe6621570bff684855c3bfe8859570fdf2a2555c3f7e8895570fdf61a555c3bfe8895570fbf99a555c3f7d8595570fdf596555c2ffeaa60570effa21815c3efe6660570eff615815c3f7e5560570effa21615c3f7e5558570bffaa9515c2ffda854570effa21515c3efe6654570fdf955515c3ff58154570ffda22115c3ff58584570ffd216115c3ff65584570eff29688582ffeaa61560dff2a585583bfe8861560fdf2a255583f7e8895560effa2255583f7d8595560fbfa2266543efe6661550effa2165543efe6660550effa2161543f7e5558550effa2151543efe6654550ffda2211543ff58584550eff29688443efe8899910bffaa9854437fca961510effa2185443efe6661510fbf99885443f7ca895510fdfa2255443bfe8895510fbf99a55443f7d8595510ffea2176803ff97661600ffe5d885803ffa885d600ffe61975803ff9855d600ffea2165803ff98759600ffe61565803ff97559600ffe5da55803ff97560600ffea2171803ff9855c600ffe21571803ffa555c600ffea2161803ff98758600ffe61561803ff88558600ffe5d561803ffa5558600ffe6a151803ffa8854600ffe69d51803ff98754600ffe61551803ff97554600aff68497a22bfda725688aff68495a227feaa65487b7f694989df9fca9a2277e7f296889dedfda825677e7fa20959df9fe8861e77e7fa227761b9fe889dd76ebf29e8899bafca5a2266bbfaa98799bafe8861e66bbf6948799aefda121e66f3f2a27799bcfe889de66f3f2967799bafe889de66f3f61e7799a7fda1a6585d7fa66776179fe889dd859ff2a5766176fe9999985ebfa2266617cfe7799985dbf9dd962176fd9799885f3f9de66217b7ca761485edf9dd85217b7d7661485df79dd932177dd7664c85dfb9dd922177ed7664885dfd69d912177f67764485dfd699912177f57664485dfd691912177f5a064485d7f9dd912176fe6664485bbf698985d73fe99a2175e7fa22775d67fca961975dbfa66665d76fd9899975ebfa22665d7cfd8799975f3f9de665d76fd9899875ebfa22661d7d7ca85d475cffa21911d76fe66644759ff2a5875979fd8721d65e7fa2277597b7e8825e55bdf68497956f7da121e55f5f2a677957d7ca89de55f5f26277957d7e889de55edfa2277957d7d879de55f5f9dd86956f7ca95da55edfa2176957d7e775da5)) else (if i < 4 then 0x75bff2a5865d77fe9961975f7f9dd865d7efc9899975fbfa22665d7dfe7761575fbf999855d7dfca89dd65f7fa2277597bfe889dd65f7f61e77597dfe7761565effa2175597dfe775d565fdf26277957f7e889de55fdf9dd86957f7c985da55fdfa2176956ffda121e55f7f2a277957bfe889de55effa2176957dfe775da55fbf21e66957efe7799a55fdf9dd85957f7d7661655fdf2a175957f7c8759655fdf9dd65957bfca5a2174effa21865d3efe8899974bffaa9855d3bfe8861574fbf999855d3efe6621574bff684855d3bfe8859574fdf2a2555d3f7e8895574fdf61a555d3bfe8895574fbf99a555d3f7d8595574fdf596555d3bfca5a2164bffaa9855937fca961564effa2185593f7ca895564fdfa2255593bfe8895564fdf61655593efe8899954fbf99985553bfe8859554fefa2176913fbd7661644fef5d885913fbe885d644fef61975913fbd855d644fefa2165913fbd8759644fef61565913fbd7559644fef5da559137fe999dd81effa2277607efc9799981fbf9de66607bfe7761581fbf99975607f7e7795581dffa6574607bfe885d181fbf99974607bfd855d181fdf95574607efe6655181fef5d644607bfca5a2171dffa66885c7dfe889dd71fbfa22665c6ffeaa61571dff2a5855c77fe9961571effa21855c7dfe7761571fbf999855c77fe9921571f7f9dc855c7efe6621571f7fa21755c7dfd855d571fdf2a2555c7f7e8895571dffa66555c7bfe8895571f7f9de555c7efe6695571fdf616555c7fbe8891171fef616445c7fbc8591171fef956445c7bfca7a2161eff29688587bfe8861d61bff69487587dfe889dd61effa2277586ffeaa61561effa2185587dfe7761561f7f9dc85587bfe885d561bff6a075587bfe881d561fdf2a255587f7e8895561fdf29e55587f7d8795561fdf21e55587f7e7795561effa2255587dfe7795561fdf61655587f7d7595561effa2184587f7e5561161effa2174587f7e555d161effa2154587f7e5555161fefa2244587fbd8791161fef61644587fbc8591161fef5d644587fbe5591161dffa66885477fe8865d51effa21975477fe9961d51dffa6487547dfd989dd51f7fa22775477fe999dd51dff66277547bfe889dd51fbf66266547efe8899951fbf65e66547efd8799951fbf21e66547efe7799951f7f9dd85547efe6661551fdfa2175547bfe885d551fbf99975547f7c8795551fdf9de55547bfe8865151fbf999945477fe9961151fbf999845477fe995d151dff66174547bfe885d151fbf99974547f7e555d151effa2154547efe6655151fef66244547fbe8891151fef65e44547fbd8791151fef61644547fbd7591151ffd65d81547ff67760551ffd65181547ff57460551effa2190547efe6664151ffd60590547bfca5a2141fbfa2266506ffeaa61541dff2a5855 else (if i < 5 then 0x5e1a4f1a401a2c9a1b5a0c59fd59ec19dad9c999b859a4d98f1980196ed95b5947d93459255911d8f9d8e418d098bd18abd8985884d87398625853584698331821d812d7fd17e757d3d7c297af179dd7881772575ed7491737d71d970e96ff96e796d416c096ad169bd6885677166396501641162fd620d60b15fc15ead5d095bad5a0958895709558954755361524d515d4f954e814d914c114b2149e948b14779466544e543ad42bd418540713f5d3e493d113bfd3b313a65392d37d136e134d133bd3285314d30152edd2ccd2b9529a927bd268524e123cd222921151fb91e5d1c711b391905173d15991485130511cd10950fa50e010d350bfd0ae909b108790741060904f503e102cd01b9005cff48fe34fcfcfbc4fa8cf954f78cf6c0f564f3e4f2d0f204f0ccef94eda8ebe0eacce970e814e694e55ce424e310e1d8e130dff8dee4ddd0dd04db60d998d83cd704d5ccd4b8d3a4d290d158d020cf54ce40cd2ccc18cabcc9a8c828c6f0c5dcc480c36cc27cc168c054bf40be2cbcf4bbe0baf0b9dcb8c8b790b6c4b5f8b4c0b388b2bcb1a8b0b8afc8aed8ada0ac8cab9caaaca998a884a770a638a524a410a2fca1c4a0689f549e409d2c9c189abc99a898949780964894ec93fc92e891b090788f408e508d188b988a3c890487cc86b88580844883348220813080647f2c7e187d287bcc7a707938782476ec75d874c4738c729c7164702c6f3c6e286cf06bb86a80694867ec66fc6558644462c4618c60545f645dc05c885b2c59f45874573c560454a853945280514850584f204e0c4cd44bc04a644950481846e045f044b843c842d8417c40683f303e1c3ce43bac3a74396038703714360034c833b432a031b030782f642e2c2d182c042acc29942880276c263424b423c4228c217820401f2c1e181d041bf01adc19a41824173415fc14e813f812c011ac10980fa80e700d5c0c240b1009fc08c4078c06780564042c0318022800f00003ffe889dd65fff9dd85597ffe8859574fff615655d3ffe889dd61fff29d85587ffe7761561fff9dc85587ffe885d561fff61575587ffc8795561fff9de55587ffe885d161fff61574587ffc855d161fff95574587ffe8855161fff61554587ffe8865d51fff66277547ffe889dd51fff9dd85547ffe8865151fff66174547ffe885d151fff61574547ffe8864151fffa21655c3ffd8559570fffa21615c3ffd8558570fff215615c3ffe5558570fff6a1515c3ffe8854570fff615515c3ffe8858550fff61561543bfca5a2277effa227761bbfca5a2176f7fa22775dbefe889de66bff68497617dfca99dd85bff2a6776177fe999dd85effa2277616ffca95d985dffa6576617bfe885d985f7f9dd76617efc9799985fbf9de66617dfe775d885fbf9de662177fe7764485dffa66885d7dfe889dd else 0x5149e2f0d2dc1e06327cb52786c5e0f03193b2f8b43cb54b83c0c651c5a1a5aa5c1e06327cb31687c1e0632664f168796a9707818ca38bc34873382149b59c758d7579f568b557754f353bb5283516f505b4f6b4e574d434c0b4aaf499b48874797473746b3457b448b442b435f4227411340b33f7b3e673d533c1b3abf39ab38df37a73693357f348f33e7331b327331cb31472feb2f8b2de72bd72b2f29d3280b2787270326a325fb252f2463232b21f3214b1fef1e031d7f1d1f1cbf1bf31b271a7f19d7192f18cf182717a3174316bf163b156f14c7141f127b11f7117310ef108f100b0f870edf0e5b0e1f0d9b0d170c4b0b7f0ab3090f0843077706630507043b036f02a301b300e7001aff4efea6fdfefc5afb46fa9ef9f6f94ef8a6f7fef756f6aef64ef5a6f522f456f3aef306f23af192f10ef066efe2ef5eed72eceeec6aec0aea8aea2ae9cae86ee7c6e6fae5c2e4f6e472e412e36ae15ae0d6e052de42dc9eda6ad9c2d91ad872d686d596d4a6d2bad0f2d04acfc6cd92cd0ecc66cbe2cb3acab6ca0ec942c89ac7f2c74ac6c6c58ec4e6c41ac22ec186c0dec012bf8ebdc6bd42bc9abbf2bb4abac6ba42b976b8ceb826b77eb6fab676b5ceb502b436b38eb30ab262b1bab112b06aafc2af1aad52ab66ab06a8f6a69ea61aa5baa3f2a206a1a6a122a0c2a0629fde9f5a9efa9e2e9d629c2a9ba69b229a7a99f699969936976e96c6949293129246917a90d2907290128f8e8f2e8ece8e268d5a8cd68b7a8a4288e6874286e286828526847e83d68256811e80767fce7f027e5a7db27d0a7c627bba7b5a7afa7a5279867926785a77d67752768675ba74a673da7332728a7206715e6f966eee6e226d566c8a6ae66a1a694e683a66de66126546647a638a62be61f26126607e5f225e7a5dae5c765baa5ade5a1257de565e559254c6541e527a51ae50e24fce4f024e5a4cb64ba24afa4a5249aa4902485a47b2470a46aa4626457e44fa449a443a439242ea4242419a401a3ee23e3a3d923cc63c1e3b763ace3a26397e38d63852378636de3636356a34c2343e33963312328e320a318630de30122f6a2ec22e1a2d722cca2c222b7a2af62a962a36298e28c2283e272a25f224ba235e222621121fda1ea21d6a1c561b1e19e618d217be16aa1572145e134a123610920f7e0e220d0e0b6a0a5608fa079e068a052e03660252011a0005fef1fdb9fca5fb91fa7df969f855f6d5f59df489f2e5f1d1f0bdefa9ee71ed5dec01eaede9d9e87de769e5e9e4b1e39de265e151e03ddf29de15dd01dc11dad9d9c5d88dd755d641d509d43dd395d239d125cfedce6dcd59cc69cb9dcaf5c9e1c8a9c795c65dc549c3edc225c0c9bf49bda5bc6dbb35ba21b87db769b5a1b469b331b21db12db019aee1adcdacddabc9aab5a97da8b1a7e5a6d1a))) else (if i < 9 then (if i < 7 then 0x2412f83c0c618672851687c1e045b191aa296c5a1c5b83c0c646a82852b818ca2f06a5393e9745e063383529f1849e0f0196609b19c1e032cc12a598ac3c670780604d50ca62f0319c13034a765e3381c14b34a62832e9545a1f07818ca4d24fa5b2a8b43e0f031949a6974aa1b1783c0c652686531587c1c6700c13b2d8ac3c670780494d50cb65317818ce0b4a72792319c1e050cc13d2a8b4325e3383c030518ca1f078096304d49a2d492d43e0f0319446a954962d0f83c0c6518c24f078143304d4aa2e3287c1e01827285268bc1e0632871aa2974962f07818ca1c6a88b52e8bc1e0632871aa0a14aa4f031943e0d22827d2e9345e063287c1a4538ca1f038348aacc502792c954922d4b83c0c650eb2511687c1c6700c13c68a04ba5516a5c1e063287552e8b524b70687c0c6511aa5d298bc1a1f031947052d8ce050d35346a974aa4514c049e0f031943acc252c612f83c0249828a932992c5a1f07818c65d2c962a5a87c1e063135426996ca64b218b43e0e3381526922cbe0f00a58c64d0cb62a5b83c0c650d35454996ca62d0f83c0c63269e28822fc1e006e2d3f0f0a602bf0780569eaecbe1d5b0bcce0f028e2f0c21cce087e6e2c2e121d0df07801aa1950b84f3383c0894fc347d151689e67078147178610e670781099dafc58870dadcce0f02134f0e20c5e670781099d8bc385c262fc1e044686bf1786d6e64278118a386c5e6427811899afc5e1b5b99c185c528e1b1799c185c526e2f3217c1e0086690b5f8ad6e642e13c1e0532162f321709e0f02762f0e17098b7078113a241c58bf07801b8b4fc587f0c4117e0f022d44821fc362c5f83c08b51c51008782170b7003747178657e0f0040569cae4be0f00ac521aaecbe2f0d4156e6707814f0d96a0a2f3383c09daf89e1b5a8bcce0f02865f178717e0f03193e5d97c3a2f07818c9f8697a2f07818c9b8bc3259243bc1e06328cb92c93c1e0630a53e5f8a50e1f078049c65197e2f0c93c0c61627cbf1787c125e30a939872fc52592783c0c6519765f178660e0f031945278bc34bf07818c9f2f49e1b1783c0c64e60c9714afc1e006cad455d97c5c1c6ead92e670781532e8b83e670781326daed6a2e0f99c1e051922592799c1e006e7e2e0ca192e67078049a3244b2495f83c028cfc5c1e4b9849e01627e2e0f25cce092ca93e4896492b70780539cc1c52bf07801b2b4fc5c1b2cc192e670781435e93c5c1a6dad92e67078155258b83e670781332f8b83abe4b83c0a651c5c195f25c1e05327abb1707c1e0532664f170757c9707814ca197c5e1c5b83c0c64f9665f0e8bc1e06327e1a5a8bc1e06326e2f0c96490d707818ca32c4b24f07818c294f96e294387c1e012719465b8bc324f0318589f2dc5e1f04978c2a4e61cb7149649e0f0319465997c5e198383c0c6 else (if i < 8 then 0x31997a38a4b24f07818c0de1e8c2e0f83c0c61272f3f170649e0630b1979f8b83e092f1854cbcfc525f07818c10e5e74822d1085c1f078097c65290c2e0f83c0c665e7c5b1707c1e06332f392d90836bf0780606b50c863b19364be0f01934516894230707804b8dd04822e0cafc1e012cad455f244f64b1588c2ab60f83c065d957e0f0237569594c96230a8b83e0f01974b5daccb64d1588c2e0f0137520daecb22f0780d69dafc1e026dad293c90472360f83c030514aa2d130742e0f00c1413e964aa4d228f46a2d128583e0f02d8dd2e9549a3d1a894262e0f83c0b0af4be0f00ad12a4cf1ba3d1a964581f078149a6af56a2d1285c1e0182374d5ead4ba4b168942e0f02375114af83e0f00925628504ba440eaf49e0f02ad41160757a4f0781569d90c76326c93c1e032e8e0f0196609092c841b5f8260e035a862b1185c1e0181373925aecbe0f0124d69dafc1e026dad2e48a0cba55168942c1f078149adaf9227d2e8b44a135b07c1e0526ca5d2a894262e0f83c0a4d2ca62b118583e0f00c1432d8ac46170780494dd145c198383c0a655e7a4b1707c1e0532af3d170660e0f0299579ca149a2e0f83c0a655e8a5d258b83e0f029957a383c0a651ed129428b83e0f0299579e96c5c1f07814cabcf4ba2e0f83c0a655e7c932992c5c1f07814c65d2c96295f83c0a626e74db2d94c96431707c1a6702a4d94d97c1e024a98c9a196c52bf07814c4dcf9265b298b83e0f0298c9a68b8350707818ccb4f8ce0f004096294cc5c1c8383c0c665a7c2d0d41c1e06332d3e258b43e0f0319969f0b4350707818ccb4e90c4d1707c1e06332d412c93c1e0630a5961f05c1e01270da79b8bc324f031858cb4fc5e1f04978c2a65a730f149649e0f031996a383c0c661b4f2f07818cc369e5486270b43e0f031996a3178962d0f83c0c665a8e0f031986d3ca4b2486b81c1c66487cb707818c24e4a6cb1278058c66486cb12f8254c664a630e149649e0f031996a1208b4b7078092c64e90cb703838cc94d8ce0f004096294c90a2e0f83c0c665a74861707c1e06332d3e2d8b83e0f0319969e87c5a963383c01025a84861687c1e06332d3e2d8b43e0f0319969f1785a1f07818ccb4e90c4d1707c1e06332d47149649c1f07801ac661a9c2e0f83c0c61272d3f170649e0630b1969f8b83e092f1854cb4fc525f07818c10e5a74822d1085c1f078096c65290c2e0f83c0c665a7c5b1707c1e06332d3a69904bc670780c99e8b433063383c025c6a827d2992c561f07818c65d34ae018319c1a94c4fa4f031945e0d4a78b14293c0c67068b52a194c961d1783c0c632e864d158696e0f03189aa09e48c6707806098974aa2d0f19c1e0182827d2c9549a451687c1c6702a8d52e9549a1b17838ce05311a452c95c1e063293446a234b22f07818ca4d04f else 0x5e0d4a727d2e8bc0c6706a53e3093c1e032cc1363383c06598254bb15878ce0f00c09da194c5e06338260694ecbc67038297694c5065d2a8b43e0f031949a49f4b6551687c1e0632934d2e954362f07818ca4d0ca62b0f838ce0182765b15878ce0f00929da196ca62f0319c1694f1b052210e86e0f0306a0a61ec8c2e130782e0f01414a3d0e86a2f07818350508bc55170983c170780a0a5154541f07809b504e8ac4e1f0d84c126e8b83e0f02b27c2783c0c1c82684b1783c0c1c8260455eadc5c973381c11006eac2e13049bc1f078120a31584c131707c1e04828c1f17254ce0f004057a11e88a67078183504f8ac2e0d174ce0f0141453107c1e015d409b9f1385c915f07c1e053288ee2b12c5c1f07814ca29889e0f0306a09b1585a660f83c0504f83e0f013aa54d4c90c4e1707c1e045e2d0fa707c1e02754a9a9a8b834ef0780a04d0e9045e270982cbe5a8bc1e060ebc5e268b83e0f012e9647d210c2e130597cb64b8383e0126bc7f170797cb64b99c024962ac7f170797cb64b99c125952acbe5b8a92c7f3097c1e0086a4870781098ee0e353b1783c084c77071a9d208843a1b83c052cf83e0f013aa54d4c9045c270b84c165f2d92e0f0307632382a51025f80969f83c04ba591ea59b1784c14832f9662f078183a93bc1e025f069a992189c2f07814cc1c768c5e258bc1e0533071da22f8bc2f07814cc1c7682bf003656e0e57113a421f89c2e1305c0c1f07115623984b24f03821bcad183e0f009395c44c4b2495f8183e094710460f11cce0124b1959f15cc25e0f8254c44f8a25f0399c110e22725924adc0c1f04a78820afc00d95b8388cacf83e070711959707c0e0e232b2a431589e053307c1c4508fc5e270bc0a660f8388a69983e0707119598208f05a2b1287432150882c97078183b82105c1c7783c08d4fc5c195c97c1e0064ad40830b922bf07801b2b51c52bf07818325864ad428524252bf0497c02b50904582b12874321508828de4b83c0c1dc0f42a130682e0f01414241170ac3e1b0b84c146f25c1e060ed4823d168ac4a1d0c844151783c0c1da8aa2a130682e0f01414241178ac3e1b0982a2f078183ad1745c1a7783c04d4f8b4561f0d84c126e8bc1c1f02b84a1d0d03e0f02373c84410ac3e1b83c081c6e990c2b0f8662f0781038dd29045e2b1187c3617098284f078183b5170942e0d3bc1e026a84793f168ac45230f86c2e130520e0f03077e2f1509c3e1b09829031783c0c1d89047a2d158942e4b83c0a660eb4521707c1a6701413c75208bc561725c1e053307562f0b922bf0707c0a6511dc5e298bc1c1f0299420f834ce015d373477178ac46154089e0f029983ae1312e0f02412c84371285f07810990512185b1783c084c8274cc4843cce0f00401ba243126642f83c084c828486268b83e0f0)) else (if i < 11 then (if i < 10 then 0x28f43a180bc1e0282745e2a8b84c1e0b83c050528fc5a2b1387c36130782a2f0781642e12d7e0f0224d61e8a9d4da2d13c1e026884be2e0bc1e025b133b21afc10870212d69e20c561b5f83c084b5a8623098bc1e0425a53f1786d784f0230d69d8acf84f039918694fc5e1b5f830b8a35a762b3f990be0c51a53b21aed6e2b3f990be0f004354878ad785c2783c06b50ca85f0399c110b2276bb1642cf6b42e13c0e6705915f1617c1e033042d79f8b0be0f0198216b4f086bc2f83c06b486787c1e0cc585f078121a3124be0c7780528d4e9d05a2241c1e026f2e9aa52185e0f022f168dcf97cb73383c01014a74ea431205e0f0137974d53455027535c1e026c745e130782cbd154196e0f02a45f07809d4da25409a231745e0f012e964dcf4541a5f83c044a5921422e0b97c4f0781969d9117e0f022c1b65ce0b847062fc08b486702c838317e045a433d5eadcce0f0040929cafc0e0958419219210fc260b8185e0e4a825d22af09e0f02ad39409043e0f00ae5632d0092412cae56e0f00cb428191c1e015cac5b9d96896470780572b16e844f0780cb504bc1e032d4121419789a2d0eafc1e055a96296cafc1e015941393e8942a2f038320a950502591c8c442122781c1295450a250b8145e0d4a7a595f8056e0d4a644f0780cb504bc1e032d4122248ad7e0a8380d69d95456230d85c1e0282844b5d9645e0f01ad3b2f12c3a2b5f83c06b505725f0780562962472290cae4be0f00ac890cd3574843d9785c260f0556e0f0313601c9ea0e655b81c10c94a94832f1584c1e0a8bc1e0626a6ba3f1784c1e09ad45e0f0313593e8b44a1d0b83c090514a62d128742e0f0241414091c1e015cac5b9e9147a35168943a142b83c010574ba2f0780572b16e7a5d1e8d44a1d0a410a62f078109b0a14aa250a8bc0e0d4a827d2e8b44a17038352a28b8350707818ccbcf8ce0f004097294cc5c1c8383c0c665e7486268b83e0f031997a09649e0f031852cb8f84e0f009387d44dc5e1927818c2c65e7e2f0f824bc61532f39878a4b24f07818ccbd1c1e06330fa89783c0c661f51292c921de070719921f2fc1e063093929b2e49e016319921b2e4be0953199298c3852592783c0c665e84822d2fc1e024b193a432fc0e0e3325363383c01025ca532428b83e0f0319979d2185c1f07818ccbcf8b62e0f83c0c665e74eb20978ce0f01933d168660c6707804b8ed04fa53258ac3e0f0318cba695c0306338352989f49e06328bc1a94f1728527818ce0d16a5432992c3a2f07818c65d0c9a2b0d2fc1e06313b413c918ce0f00c1312e9545a1e3383c030504fa592a9348a2d0f838ce0551da5d2a934362f0719c0a62748a592b83c0c652688ec4e9645e0f031949a09e4825f07818c30ce50a2d0f83c08be323b452d8b438bf07818c8ed050a5703194 else 0x240c72f07420b07420a9545a2506804b10a8232492d1287c1889045e0f0e212e1248c2e0f83c0c61432f52238b8c4bf07809e28511e83d0306247a0f40c1c913849160f8395164943e0c44822f07871213838f61c484e0e3d87113c876060c48dd282287022c05009e4a90ae4f2b44a93292cc0113c96c025124549128c11a6d95490ca04ba250a8e29988f426051252993c93424911e8939989344a151c52812e89471096496051048ac1a861c560d43c1081005c2491852286783c0a1e332c64860d43c1084b44a1b0982164906c2507042a411784c161850792e1248c2e0f83c0c61430d5c920d84a060859241b0940c14b1187c248b848360a7246171e4be0f03198630d32483517098215164943613042a411784c16185522198b8460e086924270982c30b2484e130586154886c2303042a910d84c1080f2461783c0a1e30c186264906c260849241b0943c10a49c2d0f83c0c6618c044920d84a1e0858ac1b0943c10b1583612878214a00fc592c1509246148a19e0f02878cc31f09c29160624e0f031850c31521836128782164306c250f0428860d84c108212963c9785e0f00938c30618b4822f0982c30aa443611818295228f44e10a486c14ea444e1305861496894360842792f150923e1305c0e0943255a5b1892e0f0144509e4506a06084459250d8211208bc161849142705861144866060844822f0586121709a06084a2e082a1c1b051c560d43c109158350c3a1e082a1e0824822f058611168960608425a250d8211208bc1618425c249185c1f07818c2865aa447171896e0f013850a23906a060848e41a818292230922c1b052a2c9286c1089045e0b0c24721382c3091c84e0b0c22710cc0c1085025d1690212280c58c9e49889218b294097168d0916609218b213c96c02512452812e8b48112c48a2c64b24b028a212893450c92c5644696a1a6a32812e8619949ec0a1c85224a449f4394934332c6842812e8748112c552450c42a92181439092912450e44b15491431093432ad20430b0286192cc0125a8611853496300860259258143149449a18648e0f00ae5610196722974b70be0f00925aa09e482391887c1e01868047178717e0f0217160cd2482292e2e1be0f022d4320c1c1e025d2c9b9d14c863b1897c1e032682286e2e49e0f022c50a09749a470781178b46e8a298383c08bc5a373c3f0b84c170141c1c95090c4e162fc08b70725412d0ad7e0f00c0d69d8ec64292f83c064ce052e96f83c03016a7c2d12874225f078060a087852bf07804b2b4e052595cadc1e0196765a1783c02b958b73d5c9ec96230d8556c2f0780cbad9285e0f00ae562dce5065d268785abf078156a59385e0f00ae562dce0f0501c0dc56930f99c1e0082b052210e86e0f01413c3d1785c260f05c1e02829c5e26ae4fab73383c0295) else (if i < 12 then 0x92c4e1f0922e0a0f849c9185c792f83c0c661cc34c9a0f45c16105459250f82c20a9045e130587154c8762e0983841a4d09c260b0e2c9a1384c161c55321f04c0c20aa643e0b08212d1287c2084f25e2a1246c161381c12864ab4be3125c1e028ca13c8e0f40c2088b24a1f0822411784c3892384e130e228d0ec0c2089045e130e242e1340c20945c2045025d1690212280c58c9e49899218b294097178e8917609218b213c96c02512452812e8b48112e48a2c64b24b028a212893450c92c564460f85a210e86a2d1285c1e060e94a0361f0a278645c1a4034526c227c258ac46160f83c065480a9046e24526c207a228bc1e060e98a0a3932683d0a88249a0f44a160c544d1707c1e05328ea0224d07a250b062d120f838cae9b88968947e0c407d25134542d110983a120b83c0a5a94e4822e1e1a4117830c9709c2e130459c1e5f2d9207f078050b8168843a1b8bc4e170780a5285619a42228e87a321a8b44a10438383e023ef92c3e8183104a0fa0302492c3e8183904b4b4421d0d178b44b83c0c1a3e93685e240f84b002d345e2d0922c3f073242124962b1184c16045e2d8387b2cd12c5e2cc562309830f24f030659311e8b24e0c44822f061865214b852210e86a2d1285c1e060e928f3e4b09c1c625454251e249613838d4a8f6060c44822f061a951ec0c1c8924494d1f8395138352c74425a2911831096894460c48ac23061e0cae4be0704ad95c4509045e0f10243e1505c1e2052792f15092391b0982c1f038250c45b15845030624561140c1c8578495a1183962b08c1c615c211304422512707c0e0e20a0642611838d16494460c44822f07881114494460c44aa23071a2911838d1e8a42e0f102c270715c40909c1c5710225510c0c188954460c38ac1f061c560f44c1891583d128583162b07a250b062c560f44c1891583e0c34822f078810ae954460c44aa2181839112534460e42ba5511831113834ae20447a291087432150882e0f02972030208982b1608c441c0985c1e043d966c870612210e86a2a168884a120833c1e04823772228e87a32190a84410843312a5f078183a560a16060c345a8024822d1087432150882e0f02951b301f09a2a16888481d0905c1e0242946c2a36128581830d16a00943830942a04dc68a22e0e34526c29042e1340c18b2085c268183161548c3e1b818365880885427061c2a13830c329245082447a289e1d130615130610401709445150a19e0f03074cab992183d130622401f4b4582a1288a2a1433c1e060e99473e134542c0c4dc1e053121472a4307a250b062c860f44a160c510c1e85441289830a89830942c0c1868b500457c184a15015d36228116896060c545227061b1588c260b0096219026498942f83c084c81941b2194c561305804b10c8132488624cf85b1783c084b3 else 0x4843c9e4a842210a3a3c9e4a445030a349920502441d0e45c111265341d0f826051474843c9e4a842220a3f032b880e2a8f2792a108842d0082ba3e1288429589f08a22a902812c9488840f154a93c94886042074512893088aa2064793c9308442162a3c5520504441c8f421ccd154aa220e47a130088a94c9e8924c1e848823d2668aa220e47a125478aa40a0888391c883c552a8883b0288332d401302951b0d210f27a2e144a84a0c84793d1503a0480665a8023308684c0a38b2148141170723a0e844198430741d0980a01d96a00a4890281220c8622e108922920c86c23028a3c552050244190d841d49152a9220c86c230088aa451e8924c1b08484352a48a9220c86c215475208708c0c30b21481409706436108642904306c210d80601e2a90281220c86410f152a9220cc0c10c8f25a2992243e1505c0e20525a25118511208b42e20427b2e95186491c52b95b83c0881969257022251208e46e2f1385c1e0240b7583d17094421d0d45a250e85c1e0529217601810f8508472351789c2e0f00a490a41e8b84a1d0d45a250b81c14854ac846028b1c2300c08d21c08b014047a2a40bc258016844a9747c152d899617086bf0781216b16e84421d0dc1e052d372021208b8543c41065f2dc4e1707805247d30a43a1a8884a12081f45e07064152368308a2c64547c48b50040f85c26808a161f0ba042a122a2c9488c2889045e1710243e1585c40888c2c50b84d030a242a13850c1f85089e4a4486a065d2832792a8345a40a4b449228a21409745a40819059230a432b95b83c0c4996b45929131c3e95898e1345a44709a4448a22a82347b2b131e02804f250848a0316327c24a1012032792a90192d1287c161059341f0541c20a9045e130587141e4b849230b83e0f031850c3d72683e0a8184164d07c1503))))
def layer511r11 : Packing := (839,3,6,63,0,16,1,packed511r11)
def keys511k12 (i : Nat) : Nat := (if i < 1 then 0xe64a0be081b6844d2e0d0b8eceb00b51800017f5b7247a15547d44b0a8de8eb0a38d16b9018ccaa2790ba9323293bfc52000189b5b97a262953b96187136580013190ab8194bcb9e330000f0f4a148d05265da065eeca9d328b19b2af714a4251779abe5436c3f4df553f470e5c898475d00000bb7c368001a3c083ec777926631c5913305dd78f8b58a72e99aa79e6446f1c88d0e62bbeea0b286e76f898dafae18ff1d6307cd713b261b1925cc5b50e192f276f66dcdd5667c4139a8001750561cca18001673c88c2de25cda96ca1246528820e892da45dd07f4d080000d6f61a0005d200002ab5f8e8000c5e1a54b48e4272f10cf1ebf0000aaf5dd2c8f0a570dcf688f38ddc09808001cb48000e1598e579d89d3213558eee8234da7f23f311e84af8436cff5440c0a0fc0c4cf359b64cbc2847ae731db42a5b87e80845bec44abb12c4273434b284ea7813444028f5767e639c29442800048f8000496017e667e9764a04b5bfac32109c551108001986000000006248f95cbc86458ec02c6afee52d5fa2926a2c00048194b28000f2a68ddee0a32400073a630318e20004c51d0ba917465ea26000157aaf49b1ccf0226e00000012f750378b9bda843df55f73f2b30d5d9e5643fc5254caaa60000755546969c40003b70551f46e3a2b27a678fe6228a8000642791c6d7a9f8a3cf21e469a3cd4b3f5294dbb90e115d9aff30c85b2a68001ccd31842d87339b8b6e5d523ddaa60c191bc6090add208a886f5e84be13bbc36aa93047178000c568a07641db120005086435842ae57fd34cf52a5ce85bc01546e88531719d1a1262e40002963230e4780000444000536d216090459cf9f2a5a4c6080e54f842a9518679d46a57868bfc863c38b05181b34033cb9414b8b26dedcbee3557dd6cdd49824d83219f00018c8dc34512a3b0d58e4a7e19b57308872f22028000e7d4967f3b0ad0e462a2e0007a8f844209d50090d5ab75d58a040e000040082004030000400060003c4002048042007138040000010684c070083c02390002c0401020000e0607008040000010123c0201c000e010142e1c0280c540a0000800012184800121a85412040703c0000008104e000005c20010181000041390c020b0f80400021080034010000002090000400000300002220126004064b810200e0b00008000b80014160d09c0002088305a060192c140700020320401804ba0e0001c00000d00062000c0100020048180a0c0303c00080000c0a0102000022c000d0660300000000003060260206010500001078280203034001c071380e080305c1200018a0120b120080c0b1e8080104260bc0a00008001a520884c02010e004100800014000b0400030820000c080000800145b0400804330f000320a0091c100a0081052080700c000f00804001600008060a else 0x10a4653ccf6f13e00051e8d2132f6619510a5080c9039269d64ea560b2a580004509ad4c47a000000000171b3c8d8e633e8306532c43bab89a9f89ac662620a0000c0e00043ba0002ce60000a6787f800165580000000001f64b889d0ead32b315bafec9e03bd9b9568d9440bab620000b5800c8f47f495506ae28c7c44e1893a2acc256634adec3f4d51320976df393f9c5d7182e32f52c53c9921cd1e5f75499c44d8222f33e3e700950139610b74137805c771201e58aa0ea17fe16b0feedc65530001a5ef487808bb67d3dc00e8c791b125508504534ca2a22ddacd4d8896000144e38525b817f314084b9c80000109aad8e6450512a74141a686381820df07000034480c40278a98b89e5dc756b3b8aed166cf1fc4f5cddb5a3836758ded5932efa11e4ca90ea3f765041eb05954b0030a32993a01d7a0dca48ef792036d51cc4aca5dac3ebc0978f0a31c7e80bd8b3746857ab26a25b22102f24b4943780004801df7a18696fd2aa459e71f879f84c449f269622838317c0003b9a877f2c400072fba6e160dae535e226832df229a8e6a64839e0000028e662a71a5609be76729a97593e67261cb4e21a0001233da580000001b475bce0000001e448000cb5ca680002d080007cd1b69ecc657a00011810000b4ba3fc0002b500000875504412bb01aa4ccbe513000044f203f685e0d1ce540003583349de36f79bcda4f18e1613afb09c6895f07880000a900368b3a5a457334b0ab4b099fb3b802728e20046d4800000060213572052ef41164796f1ea54c7cd8904c002f8f9ccbf79000044e89c861152e28b1f2e98b814764b0000132fb13959a4b0ee6d220ea5c60b3a98d62f52b1c9dc6029bad408000e706815153895c2a8061e00021ef4729da5a3a53abcda9a7ce8a4d0aa928001a9e13de545e9b2f5ad43152d188f74e8000f55d9475a34a3400000004a280016d6367b7542cfa0000578000783dc40acc9b8200000000890b54aa8000025aef8c0d39a0a8b4a0001c960004b3cf7b0000e1e8000a18b4b2f1c3a5fd6c6332000717e0003c898ff80ae0001c05191cad88cf9a2400021bc41f31eda540000322e0080002a1a55ffbd8e1d9b804cec2efe6691146df8640f391515d0b4b0c253b8c0000513d727de74cbb000000000000000000000730377c80b735d7ca1efb3dc316eba95d61be60b7d1581f24fa37a94ebf7b5094b76871d2beadac634d521e1d0cd923d59bb1961af1d9f353ac9ca0b5ce2c6ab84b0d800144a1be0cba8000cac7bf8475600600069332c87a9ccc055bc4cda9f7c287173908caa42103ba56946aa8983d175797c)
def packed511r12 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x65ffec2acbffd75597ff90f2afff9de55ffebb4abffd65613ffd10ba7ff61974ffec2ae9ffc855d3ffacaba7ff95574fff442c9ffd85593ff90ab27ff95564fff442a9ffd86553ffb0aaa7ff59554ffe4bb03ffe77607ffaeac0fff5d181ffeaa303ffe885c7ffb0ab8fff21571fff2aae3ffe88587ffb0eb0fff21d61fff3bac3ffd85587ff90ab0fff5d561ffe3aac3ffe55587ffb08b0fff5d161ffeaa2c3ffd98547ffd10a8fff65d51ffec3aa3ffc87547ffceea8fff61551ffebaaa3ffd94547ffb08a8fff5d151ffeaa2a3ffd90547ffd10a0fff61541ffe42a83ffe55507ffacac07ff58580ffea8b01ffe885c3ffb0cb87ff61570ffe42ae1ffd655c3ffcaab87ff60570ffeb0ae1ffd515c3ffd10b07ff61560ffe42ac1ffe55583ffd10a87ff61950ffec2aa1ffd65543ffb02a87ff58550ffea8aa1ffe88443ffb0a887ff21510fff2aa21bfc97a237f92b445ffa6587dff4430f7fd9521effb2243f7f26277eff444efdfc959df7fd113bf7f61e77dff4430ddfe7761b7fd10bb77f9dd76f7f444cdefd8799bdf90f337bf9de66bff4cb0bbfe88617bfceec2fbf99985bfecb90bdfe77217dfccc42dff64485bff4caeb7fd985d77fd10baf7f61d75eff3baebefe665d6ffb303aeffa2075f7f330eb7fd911d77fd10b2f7f9dd65fbe4c4abf7e88957ef92f2afdf61e55fbe43cabf7e77957efb0d2afdf5da55dff444abdfe77957dfccd2afdf61655fbebacabf7d659577fd10c27bf99984fbf2ab09bfe885d3dfcccba7df95574dff442c9f7e555937fd10aa7bf99954fbf2aaa9fbe88913f7b0f227ef61a44fdebb489fbd85913f790b227ef5d644fdeb2c89fbe55912ffd32c0effa2181dfec3b03dfe77607dfcccc0eff61581fbf2ab03fbe44606ffd32b8dff66171dff442e3dfe775c7dfcccb8f7f5d571fbf2aae3fbe445c77fd10b0f7f9dd61fbf2aac3fbe44586ffd32a8dff66151dff442a37fd97547bfceea8fbf99951fbebaaa3f7e55547f7c88a8ffd60551dff44283efe66507efcaaa0ffda2211ffac3c23ff487847fecef08ffd61611ffa42c23ff575847fe8eb08ffd95611ffac2423ff574847feaa908effa2180f7f33301f7e55603fec22c06ffa2170f7f332e1f7e555c3fec22b86ffa2160fbf2aac1bfe88543dfccca87df95550ffb08aa1bfe88443dfccc887df95510ffd44401ff987803ff30d007fe5da00ffcc2c01ff885803ff2eb007fe59600ffd2ac01ff981803ff2e3007fe58600ffca8c019fd8721edfb2c43e7fa2277d7f444cdcfe7799abfb2e42dbf65885dbec290b7bd94216fbb2642dfb64885bfac890b7f990217afaea3aedfa2255ebf3bcabe7e6695777d112276f9de44f5f33489f3e559137ed1108f7d9de11f7b33423f7655847f6c8908efea2200efd3bc01efa66803ef4ab007fc84600 else 0x8b4996c0c18c929c42252f170f0702325a98b89c345c1c08c96a22f170c830702325a88b5289c543c1c08c96a64842252f160f0702325aa8b894583c1c08c96a24a2d27160f0702325a9604996c5c3c1c08c4ba5245b170d830702306a949459660c0c18c52a12d26330304594a71a4b484996c5c350c1c08cac6a584523170d2f07023126b164b49c5c3c1c08c1aa52d1659270306314a84b9660c5c3c1c08c49a46926594b150f07018232a4b4952c5c1c08c431aa52d265b010f06312281a4bc596436152c1c08cab170c805f07005a7170bc1c016129a5d2f170e5b3307028c34b85ccc1c0995f0d5a173307027c5c30f0b09ccc1c0a02c273307004a6c5c310ccc1c0099f170c2c245f0700468c5c3cc09c0189b170f33042c52621c5cc0b09c1c09f170c2c245b07004e820c50fc317c1c016a3170d2c8333070275789c5c356ccc1c0a30e25173307026974bc5c3c1c08c9f170c5f070232697c345c1c08c9a5d27170f0702327c5834b92ccc1c09d5f160c6d5a4b33070294583ccc1c097160d264b3307027c5835792c1c04c9e592f170f0702327c5c316c1c08c9a5b0d1707023269649c5c3c1c08c9f150e594b0702327ad755992aff55b8aab553f2a535448a7e54e529a352d8a535497290751b8a2c543d285750509fd53ed27af4f089d5539326fb4d989a9533f265b4c6098352f725c74b3895e52a9252b4a009385253246348488f951db238746c88d0518522db45608a2512b222b43f887450d521774290846507520c34120816501720033fa87ea4fbf1f4f3e407bd4f611ea73cf87944f131dfb3b987674eb91d433a3073a4e5d1c9338d87124e0f1bfb37b86ed4dc51b6b36806c54d731ab735186964d191a0733c866e4cc9196f32986474c7b18cf31586244c31183330285fb4bdf179f2ef85d44b9716fb2d985aa4b3b164f2c4857d4ae915a32af85564a97150b29c85304a4f147b28a050b4a0713e727804e649bb135726584c3496f12b7253049949211223240047848dd119722e84544899110b21d0431484f107720a840d48030fd71f603e347b30f3b1e283bc47610e931ce039347110dff1bc036a46bf0d4f1a5033c46650ca318f0316461b0c0f17d82ee45c70b5f16682c0456d0aaf1510297451d0a1313d026e44c909731278242446f08b71118219441f08170ff01f543db078f0ed01d1439106fb0db01ae4349066f0c9818942fd05d70b6016242b1053f0a4013c4261049b08f0114421303ff07b80ec41c9037706a80ce418d02f705b80af414d027f04c8091411101ff03c006f40d1018302d00534097010f01d00344059009300e8016401f001f0000fff444efffe7761bffd10bb7ff25d85fff3bb0bffd76617ffcee42fff5d885ffe4c2ebffe885d7ffb0cbafff61575fff442cbffd87597ff90eb2fff9dd) else (if i < 3 then 0x30702bc50b091d1bc1c01aa05a215f145f0f315a2f070226c8786c3cc458bc1c089a43c1c1b154b302f070086a100a0819c589c1c01d1b1aac746b17073300806e8884bc5c3978f2096ccc1c0ac2f14270700746c806a98b89c5c1c017161ba22e265f0e3e5917330702ac5c317c1c0091610a223152f0e5e2707025a9a0c3459789c1c096a0231483045f00588688a854b20c0ccc192a03e2e155e255b0333064aa4a09c5c3c1c0cc20a3170d2f3307008270948c5c357c120c056a55f153f0d5b33070082948c589c3574bc1c056a52e27170d5f07015a84a45c0ccc120529d5d2d153e255b0333054aa8ac5c3ccc1c0209c3e2e815f170d5b33070226b8b8ac3a045ccc1c089a52b170f0733008274b094857c5c34fcc20c156c0b12d2824830333054a8c5c3c1c08c20979e270d16830702325e8c5c3c1c08c20979c42252f170f0702325e98b89c345c1c08c97a23127170e1f0702a28104b8997c0c18c92a22d265f0306324a710894bc5c3c1c08c97a62e270d170702325e88bc5c320c1c08c97a181265f170f0702312e94917c5c360c1c08c1da525165d830306314a84b498cc0c117529c752d21265f170d43070232b1d971348c5c34bc1c08c49ac5d2d27170f0702307694b459749c0c18c52a12e5d83170f0702312690f0706c592ccc1c08320a82e2b160e4b3307008290a0392ccc1c01b20a2255c6e4b155a0f33070282b8b8a8987864583ccc1c0a0ac27164b3307020c8288ac592cc83c1c020a076255e4b160f07028132a8392c5c1c01d251aa3160c770700806a710899796c54b838f92ccc1c0a5b62e264b160f07005c583ea8b8997968f83cc45c1c0a5ac271649270700760c6a9208b9796c549838f92ccc1c0a5b62e264b170701320c769108a894bc0cc83c188a62e255c6d5b03320f0622a834988ccc0c1959e2e255f020f05322280b0a83c592c1ccc021a42b164a0f0733008288a878620c54b8392ccc1a1c0b0642e260f16487707006aa8bc51b578392ccc156a1c0ae2e2a1e1a0f3117068702a190ac50357562192ccc1c01bb21e1b1648833307008691d8bc55783a192c1c04ca82f1424844b3307008299210894bc583c1c08c97aa2e25160f0702325e8928b49c583c1c08c97a52927160d824b3307012ea4b495756c59260c1c0cc1bac4b160d5e492f07015a992c557c1c01b569c6d291d192d27160d424b330702d1b124746c583cc924bc1c049b12f155d59264b0703306ea60c583579249c1c056a52d2b160d824b33070126a9249c58360c1c04c57a52d264b160f0701315e94b9249c583c1c04c57a7170f070230825a789c345a0c1c08c96a3170f070230825a75289c543a0c1c08c96a442252f170f0702325a98b89c345c1c08c96a23127170e1b07029e88b8952c543c1c08c96a4412e265b0306324a8 else (if i < 4 then 0x1265eb10496097c0c14b8c92a48d412d265f0702324a9134bc1c08c974992a08d822d2e5f030526324aac5c34bc1c08c2097a117023304825d4a70b09c5c3c1c08c2097a4822d2c14270306325d4aa12c557c1c0835620a2264b155f0702806d5a9575692c5c1c0cc201ba625311f164a0f070281a2ac54c83c1c020579c952441825f160e3e5a4b3307012ee25190f4b979649c58f839250ccc1c0a5c05c584a3f160c3e5f325a492f070126f8b4b2560c59796838f92ccc1c0a549bc422929258303320f06212eb154957564b60c0c1cc881bae255d2f020f06215a88b8957c0c11b8856a06d291d1a0d2d26214333070256d1b8a4746cc4bc083c18849ad2e555d5927030732206ea608b5749c083c18856a62d2e2928558303320f062126c150b4960c083c14c8857a8562d2e2527020f0532215eb158b4b49c083c14c8857a92b164b04833300846698a8786a1c5834b92ccc1c020b15d592c864b170703306c66ba1215756c592c1ccc0201bac4a1466860d5e4b052f015ab8bc5a19257c1c01b56a42e2928264b17060f33008066c8b4b0a92090320c5c1c0cc1b19b4652e0f1649330700855eaa18321c592c14cc02057a8862d2f160e4b070285315eb8b4b20c5c1c04c831957a8652e0f1649330700855aa10496092c583c1c08c4b97ac7a492d4127160f0633025eb1312c5834bc1c08c4997a9807a2d2e4b160f070231265ecc08cc120965298542e2683010f0631225aa614321c552c18cc02096a8412583170f0702312e5aa240b494560c0c18c9652a92d2231261b170d4307029eb110f48c5c34bc1c08c4996ac922d2d1527030632594aa248b4b60c5c3c1c08c4996ad26321b15490f0701829ea158b4b8949c043c18c4896ac862d2f150d4b070186325ab10496096c0c14b8c92a489412d265b0702324a9114bc1c08c964992a089822d2e5b030526324aac5c34bc1c08c2096a11702330482594a70b09c5c3c1c08c2096a4822d2c1427030632594aac58c43c1c020969c562d2e27010f0631225aa8b4b20c5c1c08c431996a84125824b160f0702312e5ab1c924b5049c583c18cc096ac444b160d2f070231265aa601c8b4b92c583c1c08c4996b02d23170d5f0700815a9484746c5c3cc0bc1c049a82314746f0700806a80b8fc5c39796ccc1c020a823170c645f07002c5a9c5520b1716c1c025a123152f07005c586e80f496097c5c396ccc1c04bad2183152707005c586e910894bc5c397c1c096a527158307005c586e88ac0ccc12092995c3e2e26155a830333064ab9710898f854b96c0ccc192ae2e245f03045a4a74a4960c385ccc1c04ba52d253f0d5d5a1733070182bc385574bc1c0569d2d270e155f07015a80f080706c5c3ccc1c020a82e2b170f3307008280f888b5789c5c39056ccc1c0b22a1e1a2e270e41173 else 0xf4960c5c397c1c04b96a83c2e2616815f03055a4aa10496097858f96c0ccc14b92b123170d5f070158828880f8b89c5c39057c1c056ad155e2d3e26415b3307014ab0f88c5c38bc1c0578956a83c5c59153f322f0306254ab8948c519c1c01d1b4b1aaa23165f0e5a3d2f33070082b4597968fccc1c02052a42c265c2a3f170e5b0733008066d8a4bc0ccc120929d3d5b033304824a7198985574bc0c15692a43e2d2e16255f03055a4aa0b8a4a0905ccc1c02092a93e2d2c282614815b070330664ad48c5c357c1c02056a03e2d2e83170d5f0702255aba08b4b45574f56c0ccc18952b3023304825d4a6104960c5c3c1c08c4b97a8982d2515830306325d4aa4b488c4987c5c350c1c0a8ac4c3d23170d2f070231265eb268b4b4549c0c18c9752a89a2d2d83170f07023)))
def layer511r12 : Packing := (280,2,6,63,0,15,1,packed511r12)
def keys511k13 (i : Nat) : Nat := 0x3764ad552c00000002649c000002ae9200008151847a1b60e4bf1733195cc9716904e07913ce16a4f80019dd8e1211ec0f4946a394a63c220045f988fbc9c22a13881613722fe1b0002bea603cfd56090d7cfa82dd647ab0c18cfe85480004fea7a11a1a5d174a2ab207358000000d4400000010374368002171651f5eb8058748eb0005b685a610fa3112109722810005a4400cc17a14015895d86b912989dce5ae3a825ac3978efc35f58cba240900000000c1b266000000195600077df11c93965300031c2d18c0ef6ef9615e6e398005a02e12adf221328361925bf74228b0a800034d0001da422120e0003ddfa3b17a31ed83bc02c7baa994d509200010530f16f6576c1d40010334617c2f088000b5b12a91120000000000dd48f98291a6ed1a44e072f96715b268b30b1b859ee074415c4e814905d3e7861c7e6b202e90c11a3a6f022812dc99a3e838a31b8c10b40002a9c988e2e10180021866770007b280010ff06d80030d8ea84600b8b18f469918d8e25968d772499e40004d0943c83d4b941f474b15f9924de441933800124f85898bf599041c5272eec0b2b3b49aa77516af8a33f9cc41685a08500005300a16096216420000a3b6b1659b02200011f9457a1958a018f515cd4e47f362849cdca04708120d446d8843900004f10473abe4a14430007c3822a65e21300f785803c1026296dea01ab4a936516eae796aa0a40000000006c3446ca7424120b02070006060004012d140a048d0a0304091229310000000a12075c3300240211031b00000c07050400000100042a0b01041034000800120019040002005302000404040003010101041d2b20070b002c0f000004120028000200
def packed511r13 (i : Nat) : Nat := 0x50941161cc83005d22c4881f161972d320c0416088b0cb8b8300b502c4c5865e0c02d40b14242a08132092a45890a5c7968132092a85080e185898b0c84c8302c101c34587305c18026a16204c52f0c7969906056222a0865c4c1805a916282898132092a058a8b0d04c83004d2262c3410600c2f40b13161c18030bd02c49781046129c5898b0e0c0185e816284870d149039906020b05898a5cb031e4a6418096c16284c0980e088a058a0e1a28325320c04358b124a2838300617a44c586820c0185a816262c38300616a05892d0208c2538b13161c18030b502c4928a0e0c0185a98b0c5cc830262f16196990604f0c2cc830258b0c4cc830262f161c1803268a0c94c830262d161c1803268297cf79175370e6c266861c5c95845465014c348544e4103b635c31e2cb28624820a1d31951501200e90c0090060030000ffe88ffd87ffc87ffe77ffd86ffd76ffd85ffc85ffd75ffc75ffd65ffe55ffd84ffd74ffd64ffd54ffd81ffd71ffd61ffd51ffd41ffd80ffd70ffd60ffd50ffd10bfe88dfe77efe66f7e55fbe44ff611ffa00
def layer511r13 : Packing := (33,1,6,63,0,12,1,packed511r13)
def keys511k14 (i : Nat) : Nat := 0xa39d5d248a94c1430547000000014b62399b3d60d435a0039b35ad20025d003000005c6179797882000d890dc6b355f313cce4400003432c6005a02
def packed511r14 (i : Nat) : Nat := 0x28660204bff
def layer511r14 : Packing := (1,0,6,63,0,0,1,packed511r14)
def samples511 : Array (Bits × Bits) := #[(0xc004cc07660560000000facc000066000000600d80c600000009ce700001ffffc1e64019d96000033000000c1d9960000300001ffffffff,0x40044c0366056502a4005acca05566502a802004804200140a98c6328154502ac0e64008d965052b328294040d9965054b282a4aaa94153),(0x10407001807a1800002ccccf0000078000000801201092480000e739ffffe00000200726661800003ffffff32661f800003fffff99980000,0x405000802a183000eccccf060037830018000000001248c005a5291800e3001800012226183001951800f12260b8300191800f9998c00a),(0x60098006078000000030f0f0000007fffffc3199c0631c700000f83e0000000000c079c787e000003c00001c387e1fffffc00001e1e00000,0x200880020280000298f050f0005332a0299c1199c0211c701465f83e028cc051984029c787e00531bc0298d4286a1a0531c0298de1e014ca),(0x820e000818046000003f00fffffff8000000c01e067c1f800000ffc000000000030781f807ffffffc000001fc07fe00000000001fe000000,0x20a00000004600186f500f54030f8001878400a067c1f800c1dffc00183c0307902816806ba0307c00183dfc07fe0030d80186dfe000c3a),(0x30070030fe0078000003fff0000000000000301e007801fffffff00000000000003f801fff80000000000001fff80000000000001ffffffff,0x10050030fc00780a054bffa00140aa00a055100a0028016da81560000502a8a0553f001ff7000a0a50050529fbf0000a0a9050549555282ac),(0xfffffffffffffffc038003f00007ffffffc00000000000000003fe0007ffe000000000000000000003fffe00000000000000001ffffffffffffffffe00000000,0x4028001500004e2056700000000acc0005663ee0007dee00029980000053300a663bfd60000000ac60005630ad595440ace20567000002b30),(0xfffffffffffffffffc0003fffff8000000000000000000000003fffff8000000000000000000000003ffffffffffffffffffffe0000000000000000000000000,0xfffffffffffffffffc0003ff7fd001c67800000038cf001c6783bff5f800000731e00000e63c1cc782fd7e95d945ccf82ae67c00000001ccf00e6780000733c0),(0xfffffffffffffffffffffc000000000000000000000000000003fffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000,0xfffffffffffffffefbafa800000001078000000020f000107802fd5fb57bc9243e00529487c010f80000000000010f00008780000000010f0008780000043c00),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000,0xfffffffffffffffbdd757eadfd7b1df8000aaf0abf00055f8000000000000007c0000000f8001f00000000000001f00000f80000000001f0000f80000007c000)]
def cols511 : IndexTree ColumnInfo := (.fork 20 (.fork 10 (.fork 5 (.fork 2 (.leaf [(4,0,507,0,13),(8,0,503,0,13)]) (.leaf [(1,0,510,0,12),(2,0,509,0,12),(16,0,495,0,12)])) (.fork 2 (.leaf [(64,0,447,0,12),(0,1,366,144,11)]) (.leaf [(0,16,366,129,11),(0,64,437,10,11),(32,0,479,0,11)]))) (.fork 5 (.fork 2 (.leaf [(128,0,383,0,11),(256,0,255,0,11)]) (.leaf [(17,0,494,0,11),(0,4,219,288,10),(0,8,183,320,10)])) (.fork 2 (.leaf [(0,128,364,19,10),(0,256,211,44,10)]) (.leaf [(1,16,366,128,10),(2,64,437,8,10),(16,1,366,128,10)])))) (.fork 10 (.fork 5 (.fork 2 (.leaf [(36,0,475,0,10),(66,0,445,0,10)]) (.leaf [(128,1,366,16,10),(128,16,366,1,10),(264,0,247,0,10)])) (.fork 2 (.leaf [(0,32,217,262,9),(1,128,364,18,9)]) (.leaf [(2,128,364,17,9),(3,0,508,0,9),(16,128,364,3,9)]))) (.fork 5 (.fork 2 (.leaf [(18,0,493,0,9),(32,4,219,256,9)]) (.leaf [(32,256,211,12,9),(34,0,477,0,9),(65,0,446,0,9)])) (.fork 3 (.leaf [(80,0,431,0,9),(129,0,366,0,9),(130,0,381,0,9)]) (.leaf [(144,0,366,0,9),(129,16,366,0,9),(144,1,366,0,9)])))))
def levels511 : Nat → Packing
  | 8 => layer511r8
  | 9 => layer511r9
  | 10 => layer511r10
  | 11 => layer511r11
  | 12 => layer511r12
  | 13 => layer511r13
  | 14 => layer511r14
  | _ => emptyPacking
def index511 : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 8 36 4 9 5 0 keys511k9
  | 10 => lookupWord 49 171 7 12 8 0 keys511k10
  | 11 => lookupWord 213 724 8 14 10 0 keys511k11
  | 12 => lookupWord 279 949 9 14 10 0 keys511k12
  | 13 => lookupWord 93 324 8 13 9 0 keys511k13
  | 14 => lookupWord 11 41 6 10 6 0 keys511k14
  | _ => fun _ => none
def g511 : Forest := ⟨511,14,fun j => samples511[j]?.getD (0,0),cols511,#[[]],levels511,index511,noFactory,noFactorySound 511⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom145 : graphValid g145 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice145k3p0 : block g145 3 0 1 = true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK145k3 : block g145 3 0 1=true := slice145k3p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked145 : checkedTables g145 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g145 0 0 0=true)
  · exact (rfl : block g145 1 0 0=true)
  · exact (rfl : block g145 2 0 0=true)
  · exact layerOK145k3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low145 : Lower (vars 145) (graphGoal 145) 4 :=
  lower_forest (g:=g145) (i:=0) (hints:=4) (before_sound [] baseKnown) geom145 checked145 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps145 : List (Nat × List Nat) := [(145,[]),(292,[135,84,32,16])]
def known145 := extendKnown [] 4 maps145
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid145 : Known known145 := extendKnown_ok baseKnown low145 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom102 : graphValid g102 (boundsBefore known145) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice102k3p0 : block g102 3 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK102k3 : block g102 3 0 1=true := slice102k3p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked102 : checkedTables g102 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g102 0 0 0=true)
  · exact (rfl : block g102 1 0 0=true)
  · exact (rfl : block g102 2 0 0=true)
  · exact layerOK102k3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low102 : Lower (vars 102) (graphGoal 102) 4 :=
  lower_forest (g:=g102) (i:=0) (hints:=17827152) (before_sound known145 valid145) geom102 checked102 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps102 : List (Nat × List Nat) := [(102,[]),(106,[101,50]),(163,[117,101,32]),(166,[118]),(178,[117,101,66,50]),(195,[117,32]),(202,[101,117,50]),(298,[129,113,97,49,33]),(330,[134,101,117,49,33]),(332,[133,117,49]),(354,[130,114,66,50]),(360,[133,82,114,66,49])]
def known102 := extendKnown known145 4 maps102
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid102 : Known known102 := extendKnown_ok valid145 low102 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom147 : graphValid g147 (boundsBefore known102) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice147k4p0 : block g147 4 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK147k4 : block g147 4 0 1=true := slice147k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked147 : checkedTables g147 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g147 0 0 0=true)
  · exact (rfl : block g147 1 0 0=true)
  · exact (rfl : block g147 2 0 0=true)
  · exact (rfl : block g147 3 0 0=true)
  · exact layerOK147k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low147 : Lower (vars 147) (graphGoal 147) 5 :=
  lower_forest (g:=g147) (i:=0) (hints:=116) (before_sound known102 valid102) geom147 checked147 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps147 : List (Nat × List Nat) := [(147,[]),(294,[132,116,84,32]),(300,[135,84,49,32])]
def known147 := extendKnown known102 5 maps147
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid147 : Known known147 := extendKnown_ok valid102 low147 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom181 : graphValid g181 (boundsBefore known147) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice181k5p0 : block g181 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK181k5 : block g181 5 0 1=true := slice181k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked181 : checkedTables g181 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g181 0 0 0=true)
  · exact (rfl : block g181 1 0 0=true)
  · exact (rfl : block g181 2 0 0=true)
  · exact (rfl : block g181 3 0 0=true)
  · exact (rfl : block g181 4 0 0=true)
  · exact layerOK181k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low181 : Lower (vars 181) (graphGoal 181) 6 :=
  lower_forest (g:=g181) (i:=0) (hints:=2098436) (before_sound known147 valid147) geom181 checked181 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps181 : List (Nat × List Nat) := [(181,[]),(217,[101,50]),(309,[135,84,32]),(405,[133,101]),(409,[133,101,50]),(421,[117,133,84,100,32]),(433,[133,82,98,50]),(436,[117,133,84,66,98,32,48,16])]
def known181 := extendKnown known147 6 maps181
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid181 : Known known181 := extendKnown_ok valid147 low181 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom110 : graphValid g110 (boundsBefore known181) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice110k4p0 : block g110 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK110k4 : block g110 4 0 1=true := slice110k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked110 : checkedTables g110 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g110 0 0 0=true)
  · exact (rfl : block g110 1 0 0=true)
  · exact (rfl : block g110 2 0 0=true)
  · exact (rfl : block g110 3 0 0=true)
  · exact layerOK110k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low110 : Lower (vars 110) (graphGoal 110) 5 :=
  lower_forest (g:=g110) (i:=0) (hints:=17851728) (before_sound known181 valid181) geom110 checked110 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps110 : List (Nat × List Nat) := [(110,[]),(167,[117,101,48,32]),(334,[134,101,117,49,33]),(419,[83,133,101,115,67,32]),(426,[134,114,66,81]),(458,[49,129,114,99,66,81])]
def known110 := extendKnown known181 5 maps110
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid110 : Known known110 := extendKnown_ok valid181 low110 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom227 : graphValid g227 (boundsBefore known110) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice227k4p0 : block g227 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK227k4 : block g227 4 0 1=true := slice227k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked227 : checkedTables g227 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g227 0 0 0=true)
  · exact (rfl : block g227 1 0 0=true)
  · exact (rfl : block g227 2 0 0=true)
  · exact (rfl : block g227 3 0 0=true)
  · exact layerOK227k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low227 : Lower (vars 227) (graphGoal 227) 5 :=
  lower_forest (g:=g227) (i:=0) (hints:=17825879) (before_sound known110 valid110) geom227 checked227 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps227 : List (Nat × List Nat) := [(230,[101,117,32]),(234,[118,48,32]),(482,[101,117,128,64,48,32])]
def known227 := extendKnown known110 5 maps227
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid227 : Known known227 := extendKnown_ok valid110 low227 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom362 : graphValid g362 (boundsBefore known227) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice362k5p0 : block g362 5 0 5 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice362k5p5 : block g362 5 5 10 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK362k5 : block g362 5 0 15=true := (@block_merge g362 5 0 5 10 slice362k5p0 slice362k5p5)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice362k6p0 : block g362 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK362k6 : block g362 6 0 1=true := slice362k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked362 : checkedTables g362 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g362 0 0 0=true)
  · exact (rfl : block g362 1 0 0=true)
  · exact (rfl : block g362 2 0 0=true)
  · exact (rfl : block g362 3 0 0=true)
  · exact (rfl : block g362 4 0 0=true)
  · exact layerOK362k5
  · exact layerOK362k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low362 : Lower (vars 362) (graphGoal 362) 7 :=
  lower_forest (g:=g362) (i:=0) (hints:=12902752336) (before_sound known227 valid227) geom362 checked362 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps362 : List (Nat × List Nat) := [(362,[])]
def known362 := extendKnown known227 7 maps362
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid362 : Known known362 := extendKnown_ok valid227 low362 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom179 : graphValid g179 (boundsBefore known362) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice179k5p0 : block g179 5 0 3 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice179k5p3 : block g179 5 3 4 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK179k5 : block g179 5 0 7=true := (@block_merge g179 5 0 3 4 slice179k5p0 slice179k5p3)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice179k6p0 : block g179 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK179k6 : block g179 6 0 1=true := slice179k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked179 : checkedTables g179 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g179 0 0 0=true)
  · exact (rfl : block g179 1 0 0=true)
  · exact (rfl : block g179 2 0 0=true)
  · exact (rfl : block g179 3 0 0=true)
  · exact (rfl : block g179 4 0 0=true)
  · exact layerOK179k5
  · exact layerOK179k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low179 : Lower (vars 179) (graphGoal 179) 7 :=
  lower_forest (g:=g179) (i:=0) (hints:=1048660) (before_sound known362 valid362) geom179 checked179 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps179 : List (Nat × List Nat) := [(179,[]),(211,[101]),(358,[132,84,117,100,32]),(364,[135,84,100,49,32]),(422,[132,117,100,32])]
def known179 := extendKnown known362 7 maps179
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid179 : Known known179 := extendKnown_ok valid362 low179 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom302 : graphValid g302 (boundsBefore known179) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice302k5p0 : block g302 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK302k5 : block g302 5 0 1=true := slice302k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked302 : checkedTables g302 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g302 0 0 0=true)
  · exact (rfl : block g302 1 0 0=true)
  · exact (rfl : block g302 2 0 0=true)
  · exact (rfl : block g302 3 0 0=true)
  · exact (rfl : block g302 4 0 0=true)
  · exact layerOK302k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low302 : Lower (vars 302) (graphGoal 302) 6 :=
  lower_forest (g:=g302) (i:=0) (hints:=8591017296) (before_sound known179 valid179) geom302 checked302 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps302 : List (Nat × List Nat) := [(302,[])]
def known302 := extendKnown known179 6 maps302
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid302 : Known known302 := extendKnown_ok valid179 low302 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom119 : graphValid g119 (boundsBefore known302) = true := by
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
  lower_forest (g:=g119) (i:=0) (hints:=17827156) (before_sound known302 valid302) geom119 checked119 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(315,[129,113,97,49,33]),(461,[133,116,49]),(476,[133,64,16,113,48]),(489,[84,82,132,114,49])]
def known119 := extendKnown known302 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid302 low119 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom311 : graphValid g311 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice311k6p0 : block g311 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK311k6 : block g311 6 0 1=true := slice311k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked311 : checkedTables g311 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g311 0 0 0=true)
  · exact (rfl : block g311 1 0 0=true)
  · exact (rfl : block g311 2 0 0=true)
  · exact (rfl : block g311 3 0 0=true)
  · exact (rfl : block g311 4 0 0=true)
  · exact (rfl : block g311 5 0 0=true)
  · exact layerOK311k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low311 : Lower (vars 311) (graphGoal 311) 7 :=
  lower_forest (g:=g311) (i:=0) (hints:=8590984532) (before_sound known119 valid119) geom311 checked311 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps311 : List (Nat × List Nat) := [(311,[]),(407,[117,101,132,32]),(411,[117,101,132,48,32])]
def known311 := extendKnown known119 7 maps311
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid311 : Known known311 := extendKnown_ok valid119 low311 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom413 : graphValid g413 (boundsBefore known311) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice413k6p0 : block g413 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK413k6 : block g413 6 0 1=true := slice413k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked413 : checkedTables g413 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g413 0 0 0=true)
  · exact (rfl : block g413 1 0 0=true)
  · exact (rfl : block g413 2 0 0=true)
  · exact (rfl : block g413 3 0 0=true)
  · exact (rfl : block g413 4 0 0=true)
  · exact (rfl : block g413 5 0 0=true)
  · exact layerOK413k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low413 : Lower (vars 413) (graphGoal 413) 7 :=
  lower_forest (g:=g413) (i:=0) (hints:=8589969412) (before_sound known311 valid311) geom413 checked413 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps413 : List (Nat × List Nat) := [(441,[50,82]),(473,[98,131,82])]
def known413 := extendKnown known311 7 maps413
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid413 : Known known413 := extendKnown_ok valid311 low413 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom427 : graphValid g427 (boundsBefore known413) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice427k6p0 : block g427 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK427k6 : block g427 6 0 1=true := slice427k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked427 : checkedTables g427 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g427 0 0 0=true)
  · exact (rfl : block g427 1 0 0=true)
  · exact (rfl : block g427 2 0 0=true)
  · exact (rfl : block g427 3 0 0=true)
  · exact (rfl : block g427 4 0 0=true)
  · exact (rfl : block g427 5 0 0=true)
  · exact layerOK427k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low427 : Lower (vars 427) (graphGoal 427) 7 :=
  lower_forest (g:=g427) (i:=0) (hints:=12885983319) (before_sound known413 valid413) geom427 checked427 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps427 : List (Nat × List Nat) := [(427,[]),(442,[64,32]),(459,[101,131]),(462,[16,96,80,48,113,32]),(474,[101,131,64,32])]
def known427 := extendKnown known413 7 maps427
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid427 : Known known427 := extendKnown_ok valid413 low427 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom231 : graphValid g231 (boundsBefore known427) = true := by
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
  lower_forest (g:=g231) (i:=0) (hints:=17827159) (before_sound known427 valid427) geom231 checked231 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps231 : List (Nat × List Nat) := [(231,[]),(235,[101,50]),(238,[101,117,32,48]),(246,[117,66,32,48]),(250,[117,101,66,48]),(483,[130,66,50]),(498,[32,128,66,48])]
def known231 := extendKnown known427 7 maps231
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid231 : Known known231 := extendKnown_ok valid427 low231 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom437 : graphValid g437 (boundsBefore known231) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice437k6p0 : block g437 6 0 9 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK437k6 : block g437 6 0 9=true := slice437k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice437k7p0 : block g437 7 0 6 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK437k7 : block g437 7 0 6=true := slice437k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice437k8p0 : block g437 8 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK437k8 : block g437 8 0 1=true := slice437k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked437 : checkedTables g437 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g437 0 0 0=true)
  · exact (rfl : block g437 1 0 0=true)
  · exact (rfl : block g437 2 0 0=true)
  · exact (rfl : block g437 3 0 0=true)
  · exact (rfl : block g437 4 0 0=true)
  · exact (rfl : block g437 5 0 0=true)
  · exact layerOK437k6
  · exact layerOK437k7
  · exact layerOK437k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low437 : Lower (vars 437) (graphGoal 437) 9 :=
  lower_forest (g:=g437) (i:=0) (hints:=8592033028) (before_sound known231 valid231) geom437 checked437 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps437 : List (Nat × List Nat) := [(437,[])]
def known437 := extendKnown known231 9 maps437
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid437 : Known known437 := extendKnown_ok valid231 low437 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom183 : graphValid g183 (boundsBefore known437) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice183k7p0 : block g183 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK183k7 : block g183 7 0 1=true := slice183k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked183 : checkedTables g183 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g183 0 0 0=true)
  · exact (rfl : block g183 1 0 0=true)
  · exact (rfl : block g183 2 0 0=true)
  · exact (rfl : block g183 3 0 0=true)
  · exact (rfl : block g183 4 0 0=true)
  · exact (rfl : block g183 5 0 0=true)
  · exact (rfl : block g183 6 0 0=true)
  · exact layerOK183k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low183 : Lower (vars 183) (graphGoal 183) 8 :=
  lower_forest (g:=g183) (i:=0) (hints:=1049940) (before_sound known437 valid437) geom183 checked183 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps183 : List (Nat × List Nat) := [(183,[]),(219,[101,50]),(423,[132,117,100,32]),(435,[130,98,50]),(438,[132,117,66,98,32,48])]
def known183 := extendKnown known437 8 maps183
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid183 : Known known183 := extendKnown_ok valid437 low183 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom430 : graphValid g430 (boundsBefore known183) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice430k7p0 : block g430 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK430k7 : block g430 7 0 1=true := slice430k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked430 : checkedTables g430 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g430 0 0 0=true)
  · exact (rfl : block g430 1 0 0=true)
  · exact (rfl : block g430 2 0 0=true)
  · exact (rfl : block g430 3 0 0=true)
  · exact (rfl : block g430 4 0 0=true)
  · exact (rfl : block g430 5 0 0=true)
  · exact (rfl : block g430 6 0 0=true)
  · exact layerOK430k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low430 : Lower (vars 430) (graphGoal 430) 8 :=
  lower_forest (g:=g430) (i:=0) (hints:=8859452752) (before_sound known183 valid183) geom430 checked430 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps430 : List (Nat × List Nat) := [(430,[])]
def known430 := extendKnown known183 8 maps430
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid430 : Known known430 := extendKnown_ok valid183 low430 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom243 : graphValid g243 (boundsBefore known430) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice243k7p0 : block g243 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK243k7 : block g243 7 0 1=true := slice243k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked243 : checkedTables g243 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g243 0 0 0=true)
  · exact (rfl : block g243 1 0 0=true)
  · exact (rfl : block g243 2 0 0=true)
  · exact (rfl : block g243 3 0 0=true)
  · exact (rfl : block g243 4 0 0=true)
  · exact (rfl : block g243 5 0 0=true)
  · exact (rfl : block g243 6 0 0=true)
  · exact layerOK243k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low243 : Lower (vars 243) (graphGoal 243) 8 :=
  lower_forest (g:=g243) (i:=0) (hints:=17825876) (before_sound known430 valid430) geom243 checked243 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps243 : List (Nat × List Nat) := [(243,[]),(486,[101,117,132,32])]
def known243 := extendKnown known430 8 maps243
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid243 : Known known243 := extendKnown_ok valid430 low243 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom490 : graphValid g490 (boundsBefore known243) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice490k7p0 : block g490 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK490k7 : block g490 7 0 1=true := slice490k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked490 : checkedTables g490 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g490 0 0 0=true)
  · exact (rfl : block g490 1 0 0=true)
  · exact (rfl : block g490 2 0 0=true)
  · exact (rfl : block g490 3 0 0=true)
  · exact (rfl : block g490 4 0 0=true)
  · exact (rfl : block g490 5 0 0=true)
  · exact (rfl : block g490 6 0 0=true)
  · exact layerOK490k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low490 : Lower (vars 490) (graphGoal 490) 8 :=
  lower_forest (g:=g490) (i:=0) (hints:=13171187792) (before_sound known243 valid243) geom490 checked490 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps490 : List (Nat × List Nat) := [(490,[])]
def known490 := extendKnown known243 8 maps490
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid490 : Known known490 := extendKnown_ok valid243 low490 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom366 : graphValid g366 (boundsBefore known490) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice366k5p0 : block g366 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK366k5 : block g366 5 0 1=true := slice366k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice366k6p0 : block g366 6 0 6 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice366k6p6 : block g366 6 6 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK366k6 : block g366 6 0 7=true := (@block_merge g366 6 0 6 1 slice366k6p0 slice366k6p6)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice366k7p0 : block g366 7 0 3 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice366k7p3 : block g366 7 3 4 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK366k7 : block g366 7 0 7=true := (@block_merge g366 7 0 3 4 slice366k7p0 slice366k7p3)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice366k8p0 : block g366 8 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK366k8 : block g366 8 0 1=true := slice366k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked366 : checkedTables g366 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g366 0 0 0=true)
  · exact (rfl : block g366 1 0 0=true)
  · exact (rfl : block g366 2 0 0=true)
  · exact (rfl : block g366 3 0 0=true)
  · exact (rfl : block g366 4 0 0=true)
  · exact layerOK366k5
  · exact layerOK366k6
  · exact layerOK366k7
  · exact layerOK366k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low366 : Lower (vars 366) (graphGoal 366) 9 :=
  lower_forest (g:=g366) (i:=0) (hints:=8607786320) (before_sound known490 valid490) geom366 checked366 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps366 : List (Nat × List Nat) := [(366,[])]
def known366 := extendKnown known490 9 maps366
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid366 : Known known366 := extendKnown_ok valid490 low366 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom379 : graphValid g379 (boundsBefore known366) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice379k8p0 : block g379 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK379k8 : block g379 8 0 1=true := slice379k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked379 : checkedTables g379 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g379 0 0 0=true)
  · exact (rfl : block g379 1 0 0=true)
  · exact (rfl : block g379 2 0 0=true)
  · exact (rfl : block g379 3 0 0=true)
  · exact (rfl : block g379 4 0 0=true)
  · exact (rfl : block g379 5 0 0=true)
  · exact (rfl : block g379 6 0 0=true)
  · exact (rfl : block g379 7 0 0=true)
  · exact layerOK379k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low379 : Lower (vars 379) (graphGoal 379) 9 :=
  lower_forest (g:=g379) (i:=0) (hints:=12902752340) (before_sound known366 valid366) geom379 checked379 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps379 : List (Nat × List Nat) := [(379,[])]
def known379 := extendKnown known366 9 maps379
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid379 : Known known379 := extendKnown_ok valid366 low379 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom375 : graphValid g375 (boundsBefore known379) = true := by
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
  lower_forest (g:=g375) (i:=0) (hints:=8607761748) (before_sound known379 valid379) geom375 checked375 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps375 : List (Nat × List Nat) := [(375,[]),(381,[133,49]),(471,[117,132,32]),(493,[133,116,49]),(508,[133,64,16,113,48])]
def known375 := extendKnown known379 9 maps375
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid375 : Known known375 := extendKnown_ok valid379 low375 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom477 : graphValid g477 (boundsBefore known375) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice477k7p0 : block g477 7 0 3 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK477k7 : block g477 7 0 3=true := slice477k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice477k8p0 : block g477 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK477k8 : block g477 8 0 1=true := slice477k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked477 : checkedTables g477 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g477 0 0 0=true)
  · exact (rfl : block g477 1 0 0=true)
  · exact (rfl : block g477 2 0 0=true)
  · exact (rfl : block g477 3 0 0=true)
  · exact (rfl : block g477 4 0 0=true)
  · exact (rfl : block g477 5 0 0=true)
  · exact (rfl : block g477 6 0 0=true)
  · exact layerOK477k7
  · exact layerOK477k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low477 : Lower (vars 477) (graphGoal 477) 9 :=
  lower_forest (g:=g477) (i:=0) (hints:=8640292868) (before_sound known375 valid375) geom477 checked477 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps477 : List (Nat × List Nat) := [(477,[]),(505,[82])]
def known477 := extendKnown known375 9 maps477
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid477 : Known known477 := extendKnown_ok valid375 low477 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom443 : graphValid g443 (boundsBefore known477) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice443k7p0 : block g443 7 0 9 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice443k7p9 : block g443 7 9 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK443k7 : block g443 7 0 10=true := (@block_merge g443 7 0 9 1 slice443k7p0 slice443k7p9)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice443k8p0 : block g443 8 0 5 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice443k8p5 : block g443 8 5 7 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK443k8 : block g443 8 0 12=true := (@block_merge g443 8 0 5 7 slice443k8p0 slice443k8p5)
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
  lower_forest (g:=g443) (i:=0) (hints:=12885983316) (before_sound known477 valid477) geom443 checked443 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps443 : List (Nat × List Nat) := [(443,[]),(475,[101,131])]
def known443 := extendKnown known477 10 maps443
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid443 : Known known443 := extendKnown_ok valid477 low443 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom491 : graphValid g491 (boundsBefore known443) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice491k7p0 : block g491 7 0 10 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice491k7p10 : block g491 7 10 6 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK491k7 : block g491 7 0 16=true := (@block_merge g491 7 0 10 6 slice491k7p0 slice491k7p10)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice491k8p0 : block g491 8 0 5 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice491k8p5 : block g491 8 5 11 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK491k8 : block g491 8 0 16=true := (@block_merge g491 8 0 5 11 slice491k8p0 slice491k8p5)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice491k9p0 : block g491 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK491k9 : block g491 9 0 1=true := slice491k9p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked491 : checkedTables g491 9 := by
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
  · exact layerOK491k8
  · exact layerOK491k9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low491 : Lower (vars 491) (graphGoal 491) 10 :=
  lower_forest (g:=g491) (i:=0) (hints:=12902752343) (before_sound known443 valid443) geom491 checked491 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps491 : List (Nat × List Nat) := [(491,[]),(506,[64,32])]
def known491 := extendKnown known443 10 maps491
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid491 : Known known491 := extendKnown_ok valid443 low491 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom431 : graphValid g431 (boundsBefore known491) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice431k8p0 : block g431 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK431k8 : block g431 8 0 1=true := slice431k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked431 : checkedTables g431 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g431 0 0 0=true)
  · exact (rfl : block g431 1 0 0=true)
  · exact (rfl : block g431 2 0 0=true)
  · exact (rfl : block g431 3 0 0=true)
  · exact (rfl : block g431 4 0 0=true)
  · exact (rfl : block g431 5 0 0=true)
  · exact (rfl : block g431 6 0 0=true)
  · exact (rfl : block g431 7 0 0=true)
  · exact layerOK431k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low431 : Lower (vars 431) (graphGoal 431) 9 :=
  lower_forest (g:=g431) (i:=0) (hints:=8591017303) (before_sound known491 valid491) geom431 checked431 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps431 : List (Nat × List Nat) := [(431,[]),(446,[64])]
def known431 := extendKnown known491 9 maps431
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid431 : Known known431 := extendKnown_ok valid491 low431 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom247 : graphValid g247 (boundsBefore known431) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k7p0 : block g247 7 0 9 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k7p9 : block g247 7 9 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK247k7 : block g247 7 0 10=true := (@block_merge g247 7 0 9 1 slice247k7p0 slice247k7p9)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k8p0 : block g247 8 0 5 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k8p5 : block g247 8 5 7 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK247k8 : block g247 8 0 12=true := (@block_merge g247 8 0 5 7 slice247k8p0 slice247k8p5)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k9p0 : block g247 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK247k9 : block g247 9 0 1=true := slice247k9p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked247 : checkedTables g247 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g247 0 0 0=true)
  · exact (rfl : block g247 1 0 0=true)
  · exact (rfl : block g247 2 0 0=true)
  · exact (rfl : block g247 3 0 0=true)
  · exact (rfl : block g247 4 0 0=true)
  · exact (rfl : block g247 5 0 0=true)
  · exact (rfl : block g247 6 0 0=true)
  · exact layerOK247k7
  · exact layerOK247k8
  · exact layerOK247k9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low247 : Lower (vars 247) (graphGoal 247) 10 :=
  lower_forest (g:=g247) (i:=0) (hints:=17827156) (before_sound known431 valid431) geom247 checked247 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps247 : List (Nat × List Nat) := [(247,[]),(251,[101,50]),(487,[117,132,32]),(499,[130,50]),(502,[117,66,130,32,48])]
def known247 := extendKnown known431 10 maps247
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid247 : Known known247 := extendKnown_ok valid431 low247 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom445 : graphValid g445 (boundsBefore known247) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice445k9p0 : block g445 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK445k9 : block g445 9 0 1=true := slice445k9p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked445 : checkedTables g445 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g445 0 0 0=true)
  · exact (rfl : block g445 1 0 0=true)
  · exact (rfl : block g445 2 0 0=true)
  · exact (rfl : block g445 3 0 0=true)
  · exact (rfl : block g445 4 0 0=true)
  · exact (rfl : block g445 5 0 0=true)
  · exact (rfl : block g445 6 0 0=true)
  · exact (rfl : block g445 7 0 0=true)
  · exact (rfl : block g445 8 0 0=true)
  · exact layerOK445k9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low445 : Lower (vars 445) (graphGoal 445) 10 :=
  lower_forest (g:=g445) (i:=0) (hints:=8592065796) (before_sound known247 valid247) geom445 checked445 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps445 : List (Nat × List Nat) := [(445,[])]
def known445 := extendKnown known247 10 maps445
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid445 : Known known445 := extendKnown_ok valid247 low445 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom439 : graphValid g439 (boundsBefore known445) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice439k7p0 : block g439 7 0 12 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK439k7 : block g439 7 0 12=true := slice439k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice439k8p0 : block g439 8 0 13 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice439k8p13 : block g439 8 13 18 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice439k8p31 : block g439 8 31 9 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK439k8 : block g439 8 0 40=true := (@block_merge g439 8 0 31 9 (@block_merge g439 8 0 13 18 slice439k8p0 slice439k8p13) slice439k8p31)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice439k9p0 : block g439 9 0 6 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice439k9p6 : block g439 9 6 16 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK439k9 : block g439 9 0 22=true := (@block_merge g439 9 0 6 16 slice439k9p0 slice439k9p6)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice439k10p0 : block g439 10 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK439k10 : block g439 10 0 1=true := slice439k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked439 : checkedTables g439 10 := by
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
  · exact layerOK439k8
  · exact layerOK439k9
  · exact layerOK439k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low439 : Lower (vars 439) (graphGoal 439) 11 :=
  lower_forest (g:=g439) (i:=0) (hints:=8590984532) (before_sound known445 valid445) geom439 checked439 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps439 : List (Nat × List Nat) := [(439,[])]
def known439 := extendKnown known445 11 maps439
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid439 : Known known439 := extendKnown_ok valid445 low439 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom494 : graphValid g494 (boundsBefore known439) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice494k6p0 : block g494 6 0 7 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK494k6 : block g494 6 0 7=true := slice494k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice494k7p0 : block g494 7 0 51 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice494k7p51 : block g494 7 51 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK494k7 : block g494 7 0 115=true := (@block_merge g494 7 0 51 64 slice494k7p0 slice494k7p51)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice494k8p0 : block g494 8 0 27 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice494k8p27 : block g494 8 27 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice494k8p91 : block g494 8 91 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice494k8p155 : block g494 8 155 63 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK494k8 : block g494 8 0 218=true := (@block_merge g494 8 0 155 63 (@block_merge g494 8 0 91 64 (@block_merge g494 8 0 27 64 slice494k8p0 slice494k8p27) slice494k8p91) slice494k8p155)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice494k9p0 : block g494 9 0 8 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice494k9p8 : block g494 9 8 17 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK494k9 : block g494 9 0 25=true := (@block_merge g494 9 0 8 17 slice494k9p0 slice494k9p8)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice494k10p0 : block g494 10 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK494k10 : block g494 10 0 1=true := slice494k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked494 : checkedTables g494 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g494 0 0 0=true)
  · exact (rfl : block g494 1 0 0=true)
  · exact (rfl : block g494 2 0 0=true)
  · exact (rfl : block g494 3 0 0=true)
  · exact (rfl : block g494 4 0 0=true)
  · exact (rfl : block g494 5 0 0=true)
  · exact layerOK494k6
  · exact layerOK494k7
  · exact layerOK494k8
  · exact layerOK494k9
  · exact layerOK494k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low494 : Lower (vars 494) (graphGoal 494) 11 :=
  lower_forest (g:=g494) (i:=0) (hints:=8876221776) (before_sound known439 valid439) geom494 checked494 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps494 : List (Nat × List Nat) := [(494,[])]
def known494 := extendKnown known439 11 maps494
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid494 : Known known494 := extendKnown_ok valid439 low494 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom479 : graphValid g479 (boundsBefore known494) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice479k10p0 : block g479 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK479k10 : block g479 10 0 1=true := slice479k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked479 : checkedTables g479 10 := by
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
  · exact layerOK479k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low479 : Lower (vars 479) (graphGoal 479) 11 :=
  lower_forest (g:=g479) (i:=0) (hints:=8606738532) (before_sound known494 valid494) geom479 checked479 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps479 : List (Nat × List Nat) := [(479,[])]
def known479 := extendKnown known494 11 maps479
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid479 : Known known479 := extendKnown_ok valid494 low479 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom509 : graphValid g509 (boundsBefore known479) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice509k8p0 : block g509 8 0 9 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK509k8 : block g509 8 0 9=true := slice509k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice509k9p0 : block g509 9 0 12 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice509k9p12 : block g509 9 12 12 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK509k9 : block g509 9 0 24=true := (@block_merge g509 9 0 12 12 slice509k9p0 slice509k9p12)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice509k10p0 : block g509 10 0 6 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice509k10p6 : block g509 10 6 4 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK509k10 : block g509 10 0 10=true := (@block_merge g509 10 0 6 4 slice509k10p0 slice509k10p6)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice509k11p0 : block g509 11 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK509k11 : block g509 11 0 1=true := slice509k11p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked509 : checkedTables g509 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g509 0 0 0=true)
  · exact (rfl : block g509 1 0 0=true)
  · exact (rfl : block g509 2 0 0=true)
  · exact (rfl : block g509 3 0 0=true)
  · exact (rfl : block g509 4 0 0=true)
  · exact (rfl : block g509 5 0 0=true)
  · exact (rfl : block g509 6 0 0=true)
  · exact (rfl : block g509 7 0 0=true)
  · exact layerOK509k8
  · exact layerOK509k9
  · exact layerOK509k10
  · exact layerOK509k11
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low509 : Lower (vars 509) (graphGoal 509) 12 :=
  lower_forest (g:=g509) (i:=0) (hints:=8642389252) (before_sound known479 valid479) geom509 checked509 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps509 : List (Nat × List Nat) := [(509,[])]
def known509 := extendKnown known479 12 maps509
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid509 : Known known509 := extendKnown_ok valid479 low509 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known509) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice383k10p0 : block g383 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK383k10 : block g383 10 0 1=true := slice383k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked383 : checkedTables g383 10 := by
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
  · exact (rfl : block g383 9 0 0=true)
  · exact layerOK383k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 11 :=
  lower_forest (g:=g383) (i:=0) (hints:=8607786324) (before_sound known509 valid509) geom383 checked383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[])]
def known383 := extendKnown known509 11 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid509 low383 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom255 : graphValid g255 (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k10p0 : block g255 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k10 : block g255 10 0 1=true := slice255k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked255 : checkedTables g255 10 := by
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
  · exact (rfl : block g255 8 0 0=true)
  · exact (rfl : block g255 9 0 0=true)
  · exact layerOK255k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 11 :=
  lower_forest (g:=g255) (i:=0) (hints:=17851732) (before_sound known383 valid383) geom255 checked255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[])]
def known255 := extendKnown known383 11 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid383 low255 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom507 : graphValid g507 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k7p0 : block g507 7 0 4 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK507k7 : block g507 7 0 4=true := slice507k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k8p0 : block g507 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k8p1 : block g507 8 1 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k8p65 : block g507 8 65 26 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k8p91 : block g507 8 91 2 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK507k8 : block g507 8 0 93=true := (@block_merge g507 8 0 91 2 (@block_merge g507 8 0 65 26 (@block_merge g507 8 0 1 64 slice507k8p0 slice507k8p1) slice507k8p65) slice507k8p91)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k9p0 : block g507 9 0 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k9p64 : block g507 9 64 12 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k9p76 : block g507 9 76 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k9p140 : block g507 9 140 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k9p204 : block g507 9 204 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k9p268 : block g507 9 268 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k9p332 : block g507 9 332 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k9p396 : block g507 9 396 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k9p460 : block g507 9 460 34 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k9p494 : block g507 9 494 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k9p558 : block g507 9 558 1 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK507k9 : block g507 9 0 559=true := (@block_merge g507 9 0 558 1 (@block_merge g507 9 0 494 64 (@block_merge g507 9 0 460 34 (@block_merge g507 9 0 396 64 (@block_merge g507 9 0 332 64 (@block_merge g507 9 0 268 64 (@block_merge g507 9 0 204 64 (@block_merge g507 9 0 140 64 (@block_merge g507 9 0 76 64 (@block_merge g507 9 0 64 12 slice507k9p0 slice507k9p64) slice507k9p76) slice507k9p140) slice507k9p204) slice507k9p268) slice507k9p332) slice507k9p396) slice507k9p460) slice507k9p494) slice507k9p558)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k10p0 : block g507 10 0 35 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k10p35 : block g507 10 35 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k10p99 : block g507 10 99 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k10p163 : block g507 10 163 43 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k10p206 : block g507 10 206 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k10p270 : block g507 10 270 59 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK507k10 : block g507 10 0 329=true := (@block_merge g507 10 0 270 59 (@block_merge g507 10 0 206 64 (@block_merge g507 10 0 163 43 (@block_merge g507 10 0 99 64 (@block_merge g507 10 0 35 64 slice507k10p0 slice507k10p35) slice507k10p99) slice507k10p163) slice507k10p206) slice507k10p270)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k11p0 : block g507 11 0 8 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k11p8 : block g507 11 8 31 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK507k11 : block g507 11 0 39=true := (@block_merge g507 11 0 8 31 slice507k11p0 slice507k11p8)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice507k12p0 : block g507 12 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK507k12 : block g507 12 0 1=true := slice507k12p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked507 : checkedTables g507 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g507 0 0 0=true)
  · exact (rfl : block g507 1 0 0=true)
  · exact (rfl : block g507 2 0 0=true)
  · exact (rfl : block g507 3 0 0=true)
  · exact (rfl : block g507 4 0 0=true)
  · exact (rfl : block g507 5 0 0=true)
  · exact (rfl : block g507 6 0 0=true)
  · exact layerOK507k7
  · exact layerOK507k8
  · exact layerOK507k9
  · exact layerOK507k10
  · exact layerOK507k11
  · exact layerOK507k12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low507 : Lower (vars 507) (graphGoal 507) 13 :=
  lower_forest (g:=g507) (i:=0) (hints:=12902752340) (before_sound known255 valid255) geom507 checked507 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps507 : List (Nat × List Nat) := [(507,[])]
def known507 := extendKnown known255 13 maps507
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid507 : Known known507 := extendKnown_ok valid255 low507 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom495 : graphValid g495 (boundsBefore known507) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice495k11p0 : block g495 11 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK495k11 : block g495 11 0 1=true := slice495k11p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked495 : checkedTables g495 11 := by
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
  · exact (rfl : block g495 8 0 0=true)
  · exact (rfl : block g495 9 0 0=true)
  · exact (rfl : block g495 10 0 0=true)
  · exact layerOK495k11
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low495 : Lower (vars 495) (graphGoal 495) 12 :=
  lower_forest (g:=g495) (i:=0) (hints:=8607786327) (before_sound known507 valid507) geom495 checked495 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps495 : List (Nat × List Nat) := [(495,[]),(510,[64])]
def known495 := extendKnown known507 12 maps495
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid495 : Known known495 := extendKnown_ok valid507 low495 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom503 : graphValid g503 (boundsBefore known495) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k7p0 : block g503 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK503k7 : block g503 7 0 1=true := slice503k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k8p0 : block g503 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k8p1 : block g503 8 1 62 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK503k8 : block g503 8 0 63=true := (@block_merge g503 8 0 1 62 slice503k8p0 slice503k8p1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k9p0 : block g503 9 0 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k9p64 : block g503 9 64 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k9p65 : block g503 9 65 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k9p129 : block g503 9 129 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k9p193 : block g503 9 193 55 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k9p248 : block g503 9 248 11 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK503k9 : block g503 9 0 259=true := (@block_merge g503 9 0 248 11 (@block_merge g503 9 0 193 55 (@block_merge g503 9 0 129 64 (@block_merge g503 9 0 65 64 (@block_merge g503 9 0 64 1 slice503k9p0 slice503k9p64) slice503k9p65) slice503k9p129) slice503k9p193) slice503k9p248)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k10p0 : block g503 10 0 34 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k10p34 : block g503 10 34 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k10p98 : block g503 10 98 44 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k10p142 : block g503 10 142 42 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK503k10 : block g503 10 0 184=true := (@block_merge g503 10 0 142 42 (@block_merge g503 10 0 98 44 (@block_merge g503 10 0 34 64 slice503k10p0 slice503k10p34) slice503k10p98) slice503k10p142)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k11p0 : block g503 11 0 9 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k11p9 : block g503 11 9 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK503k11 : block g503 11 0 33=true := (@block_merge g503 11 0 9 24 slice503k11p0 slice503k11p9)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k12p0 : block g503 12 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK503k12 : block g503 12 0 1=true := slice503k12p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked503 : checkedTables g503 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g503 0 0 0=true)
  · exact (rfl : block g503 1 0 0=true)
  · exact (rfl : block g503 2 0 0=true)
  · exact (rfl : block g503 3 0 0=true)
  · exact (rfl : block g503 4 0 0=true)
  · exact (rfl : block g503 5 0 0=true)
  · exact (rfl : block g503 6 0 0=true)
  · exact layerOK503k7
  · exact layerOK503k8
  · exact layerOK503k9
  · exact layerOK503k10
  · exact layerOK503k11
  · exact layerOK503k12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low503 : Lower (vars 503) (graphGoal 503) 13 :=
  lower_forest (g:=g503) (i:=0) (hints:=8607761748) (before_sound known495 valid495) geom503 checked503 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps503 : List (Nat × List Nat) := [(503,[])]
def known503 := extendKnown known495 13 maps503
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid503 : Known known503 := extendKnown_ok valid495 low503 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom447 : graphValid g447 (boundsBefore known503) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice447k11p0 : block g447 11 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK447k11 : block g447 11 0 1=true := slice447k11p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked447 : checkedTables g447 11 := by
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
  · exact (rfl : block g447 10 0 0=true)
  · exact layerOK447k11
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low447 : Lower (vars 447) (graphGoal 447) 12 :=
  lower_forest (g:=g447) (i:=0) (hints:=8591017300) (before_sound known503 valid503) geom447 checked447 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps447 : List (Nat × List Nat) := [(447,[])]
def known447 := extendKnown known503 12 maps447
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid447 : Known known447 := extendKnown_ok valid503 low447 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom511 : graphValid g511 (boundsBefore known447) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k8p0 : block g511 8 0 26 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k8 : block g511 8 0 26=true := slice511k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p0 : block g511 9 0 22 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p22 : block g511 9 22 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p86 : block g511 9 86 58 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p144 : block g511 9 144 5 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k9 : block g511 9 0 149=true := (@block_merge g511 9 0 144 5 (@block_merge g511 9 0 86 58 (@block_merge g511 9 0 22 64 slice511k9p0 slice511k9p22) slice511k9p86) slice511k9p144)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p0 : block g511 10 0 9 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p9 : block g511 10 9 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p73 : block g511 10 73 40 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p113 : block g511 10 113 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p177 : block g511 10 177 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p241 : block g511 10 241 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p305 : block g511 10 305 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p369 : block g511 10 369 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p433 : block g511 10 433 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p497 : block g511 10 497 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p561 : block g511 10 561 45 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p606 : block g511 10 606 33 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k10 : block g511 10 0 639=true := (@block_merge g511 10 0 606 33 (@block_merge g511 10 0 561 45 (@block_merge g511 10 0 497 64 (@block_merge g511 10 0 433 64 (@block_merge g511 10 0 369 64 (@block_merge g511 10 0 305 64 (@block_merge g511 10 0 241 64 (@block_merge g511 10 0 177 64 (@block_merge g511 10 0 113 64 (@block_merge g511 10 0 73 40 (@block_merge g511 10 0 9 64 slice511k10p0 slice511k10p9) slice511k10p73) slice511k10p113) slice511k10p177) slice511k10p241) slice511k10p305) slice511k10p369) slice511k10p433) slice511k10p497) slice511k10p561) slice511k10p606)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p0 : block g511 11 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p1 : block g511 11 1 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p65 : block g511 11 65 10 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p75 : block g511 11 75 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p139 : block g511 11 139 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p203 : block g511 11 203 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p267 : block g511 11 267 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p331 : block g511 11 331 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p395 : block g511 11 395 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p459 : block g511 11 459 9 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p468 : block g511 11 468 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p532 : block g511 11 532 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p596 : block g511 11 596 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p660 : block g511 11 660 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p724 : block g511 11 724 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p788 : block g511 11 788 13 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p801 : block g511 11 801 38 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k11 : block g511 11 0 839=true := (@block_merge g511 11 0 801 38 (@block_merge g511 11 0 788 13 (@block_merge g511 11 0 724 64 (@block_merge g511 11 0 660 64 (@block_merge g511 11 0 596 64 (@block_merge g511 11 0 532 64 (@block_merge g511 11 0 468 64 (@block_merge g511 11 0 459 9 (@block_merge g511 11 0 395 64 (@block_merge g511 11 0 331 64 (@block_merge g511 11 0 267 64 (@block_merge g511 11 0 203 64 (@block_merge g511 11 0 139 64 (@block_merge g511 11 0 75 64 (@block_merge g511 11 0 65 10 (@block_merge g511 11 0 1 64 slice511k11p0 slice511k11p1) slice511k11p65) slice511k11p75) slice511k11p139) slice511k11p203) slice511k11p267) slice511k11p331) slice511k11p395) slice511k11p459) slice511k11p468) slice511k11p532) slice511k11p596) slice511k11p660) slice511k11p724) slice511k11p788) slice511k11p801)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k12p0 : block g511 12 0 31 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k12p31 : block g511 12 31 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k12p95 : block g511 12 95 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k12p159 : block g511 12 159 20 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k12p179 : block g511 12 179 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k12p243 : block g511 12 243 37 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k12 : block g511 12 0 280=true := (@block_merge g511 12 0 243 37 (@block_merge g511 12 0 179 64 (@block_merge g511 12 0 159 20 (@block_merge g511 12 0 95 64 (@block_merge g511 12 0 31 64 slice511k12p0 slice511k12p31) slice511k12p95) slice511k12p159) slice511k12p179) slice511k12p243)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k13p0 : block g511 13 0 7 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k13p7 : block g511 13 7 26 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k13 : block g511 13 0 33=true := (@block_merge g511 13 0 7 26 slice511k13p0 slice511k13p7)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k14p0 : block g511 14 0 1 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k14 : block g511 14 0 1=true := slice511k14p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked511 : checkedTables g511 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g511 0 0 0=true)
  · exact (rfl : block g511 1 0 0=true)
  · exact (rfl : block g511 2 0 0=true)
  · exact (rfl : block g511 3 0 0=true)
  · exact (rfl : block g511 4 0 0=true)
  · exact (rfl : block g511 5 0 0=true)
  · exact (rfl : block g511 6 0 0=true)
  · exact (rfl : block g511 7 0 0=true)
  · exact layerOK511k8
  · exact layerOK511k9
  · exact layerOK511k10
  · exact layerOK511k11
  · exact layerOK511k12
  · exact layerOK511k13
  · exact layerOK511k14
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low511 : Lower (vars 511) (graphGoal 511) 15 :=
  lower_forest (g:=g511) (i:=0) (hints:=8607786324) (before_sound known447 valid447) geom511 checked511 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps511 : List (Nat × List Nat) := [(511,[])]
def known511 := extendKnown known447 15 maps511
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid511 : Known known511 := extendKnown_ok valid447 low511 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exactLower : ∀ t, PEqualNP.MetaComplexity.HasCircuitSize 9 edge10969 t → 15 ≤ t :=
  conclude10969 (root_index (g:=g511) (before_sound known447 valid447) geom511 checked511 (k:=14) (by decide) (i:=0) (by decide +kernel))

end PEqualNP.Outside.L_meta_10968

theorem PEqualNP.Outside.L_meta_10968 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8)) t → 15 ≤ t := PEqualNP.Outside.L_meta_10968.exactLower

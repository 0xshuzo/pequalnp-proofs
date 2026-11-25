import PEqualNP.Defs

-- Live-frontier checking adapts the proof by PressF10 from pequalnp-proofs PR 4332.
namespace PEqualNP.Outside.L_meta_9399
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 44
def zero : Sig := 0
def one : Sig := BitVec.allOnes 44
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

def Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | 0,t,S => t=0 ∧ S={target} ∧ proper target
  | k+1,t,S =>
    (∃ (u : Nat) (U : Finset Sig) (a : Sig), t=u+1 ∧ S=insert a U ∧ proper a ∧
      neg a ∉ insert a U ∧ Live target k u (insert (neg a) U)) ∨
    (∃ (U : Finset Sig) (a b : Sig) (d : Bool), S=insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live target k t (insert (bin d a b) U))
theorem Live.stop {target : Sig} (hp : proper target) : Live target 0 0 {target} := ⟨rfl,rfl,hp⟩
theorem Live.unary {target : Sig} {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
    (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
    Live target (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
    Live target (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {target : Sig} {motive : ∀ (k t : Nat) (S : Finset Sig), Live target k t S → Prop}
    (stop : ∀ (hp : proper target), motive 0 0 {target} (Live.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)),
      motive k t (insert (neg a) U) tail → motive (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)),
      motive k t (insert (bin d a b) U) tail →
      motive (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset Sig} (h : Live target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using Live.ind with
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

def bit (i : Fin 44) (a : Sig) : Bool := a.getLsbD i.val
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




def witnessM (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_repM {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witnessM w (bin d a b) := by
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
  exact Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩

private lemma gate_repM (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witnessM w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  cases l with
  | nil =>
    rcases ho with rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witnessM w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witnessM w (w.getD i zero)) (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_repM false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_repM true (get_rep w i) (get_rep w j)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.


private lemma pull_gateM {w : List Sig} {z : Sig} {k S} (h : Live target k 0 S)
    (hz : represented w z ∨ witnessM w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+1 ∧ Live target k' 0 S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k 0 (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extractM (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k S, k ≤ gs.length ∧ Live target k 0 S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gateM ht (gate_repM w g (legal g (by simp))) hs
    exact ⟨l,T,by simp; omega,hu,hT⟩

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

abbrev Row := Fin 44
theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def ImpossibleM (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → t=0 → ¬Live T k t S

theorem enum_stepM {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      ImpossibleM T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    ImpossibleM T cap ws.toFinset := by
  classical
  intro k t hk ht h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail _ => omega
  | @binary k t U a b d ha hb hab hf tail _ =>
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
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) ht (eq.symm ▸ tail)

def target : Sig := 4194303
def inputs : List Sig := [2483132825727,4970493525888,16384,32768,10138559643648,2483133285248,4970497179655,1024,8,10138555578480]
def column (w : Sig) := w &&& ~~~(w >>> 22)
def mass : List Sig → Sig
  | [] => 0
  | w::ws => column w ||| mass ws

theorem in_mass {w : Sig} {ws : List Sig} {i : Nat} (hw : w∈ws)
    (h : (column w).getLsbD i=true) : (mass ws).getLsbD i=true := by
  induction ws with
  | nil => simp at hw
  | cons a l ih =>
    rcases List.mem_cons.mp hw with rfl | hm
    · simp [mass,h]
    · simp [mass,ih hm]

theorem enough {k t ws} (z : Live target k t (List.toFinset ws)) (none : t=0) :
    (mass ws &&& target)=target := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and]
  by_cases p : target.getLsbD i=true
  · have geom : ∀ r : Fin 44,bit r target=true →
        r.val+22<44 ∧ bit (Fin.ofNat 44 (r.val+22)) target=false := by decide +kernel
    obtain ⟨hv,hn⟩ := geom ⟨i,hi⟩ p
    obtain ⟨v,hm,hp,hh⟩ := mono_row_difference (r := ⟨i,hi⟩) (s := Fin.ofNat 44 (i+22)) z none p hn
    have hn' : v.getLsbD (i+22)=false := by
      change v.getLsbD ((i+22)%44)=false at hh
      rwa [Nat.mod_eq_of_lt hv] at hh
    have col : (column v).getLsbD i=true := by
      change v.getLsbD i=true at hp
      simp [column,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_not,hi,hp,hn',Nat.add_comm 22 i]
    simp [p,in_mass (List.mem_toFinset.mp hm) col]
  · simp [Bool.eq_false_iff.mpr p]

def both (f : Bool → Bool) := f false && f true
theorem both_at {f : Bool → Bool} (ok : both f=true) (v : Bool) : f v=true := by
  cases v
  · exact (Bool.and_eq_true_iff.mp ok).1
  · exact (Bool.and_eq_true_iff.mp ok).2

instance (v : Sig) : Decidable (proper v) := inferInstanceAs (Decidable (v≠zero ∧ v≠one))

def rule (visit : List Sig → Bool) (cap : Nat) (ws : List Sig) (a b : Sig) (op ia ib : Bool) :=
  let z := bin op a b
  let c := childTwo ws a b op ia ib
  if z∉ws ∧ proper z ∧ c.length≤cap then
    if mass c &&& target = target then visit c else true
  else true

def checks (visit : List Sig → Bool) (cap : Nat) (ws : List Sig) :=
  decide (target∉ws) && ws.all fun a => ws.all fun b =>
    if a<b then both fun op => both fun ia => both fun ib => rule visit cap ws a b op ia ib else true

theorem child_swap {ws : List Sig} (nd : ws.Nodup) (a b : Sig) (op ia ib : Bool) :
    (childTwo ws a b op ia ib).toFinset=(childTwo ws b a op ib ia).toFinset ∧
    (childTwo ws a b op ia ib).length=(childTwo ws b a op ib ia).length := by
  have val : ((ws.erase a).erase b).toFinset=((ws.erase b).erase a).toFinset := by
    rw [erase_fin (nd.erase _) _,erase_fin (nd.erase _) _,erase_fin nd _,erase_fin nd _]
    ext i
    simp only [Finset.mem_erase]
    tauto
  have len : ((ws.erase a).erase b).length=((ws.erase b).erase a).length := by
    rw [←List.toFinset_card_of_nodup ((nd.erase _).erase _),val,
      List.toFinset_card_of_nodup ((nd.erase _).erase _)]
  cases ia <;> cases ib <;> simp [childTwo,kept,bin_comm op a b,val,len,Finset.insert_comm]

theorem node_sound (cap : Nat) (ws : List Sig) (nd : ws.Nodup) (visit : List Sig → Bool)
    (h : checks visit cap ws=true)
    (cert : ∀ xs,visit xs=true → ImpossibleM target (cap-1) xs.toFinset) :
    ImpossibleM target cap ws.toFinset := by
  have parts := Bool.and_eq_true_iff.mp h
  apply enum_stepM nd (of_decide_eq_true parts.1)
  have ordered (a b : Sig) (am : a∈ws) (bm : b∈ws) (ab : a<b) (op ia ib : Bool)
      (fresh : bin op a b∉ws) (proper' : proper (bin op a b))
      (len : (childTwo ws a b op ia ib).length≤cap) :
      ImpossibleM target (cap-1) (childTwo ws a b op ia ib).toFinset := by
    have entry := List.all_eq_true.mp (List.all_eq_true.mp parts.2 a am) b bm
    rw [if_pos ab] at entry
    have check := both_at (both_at (both_at entry op) ia) ib
    unfold rule at check
    try dsimp only at check
    rw [if_pos ⟨fresh,proper',len⟩] at check
    split at check
    · exact cert _ check
    · intro k t le none live
      rename_i no
      exact no (enough live none)
  intro a am b bm op ia ib ne fresh hp len
  by_cases ab : a<b
  · exact ordered a b am bm ab op ia ib fresh hp len
  · have ba : b<a := by
      change b.toNat < a.toNat
      change ¬a.toNat < b.toNat at ab
      have different : a.toNat ≠ b.toNat := fun e => ne (BitVec.eq_of_toNat_eq e)
      omega
    have swap := child_swap nd a b op ia ib
    rw [swap.1]
    apply ordered b a bm am ba op ib ia
    · rwa [bin_comm op b a]
    · rwa [bin_comm op b a]
    · rwa [←swap.2]



abbrev Level := List (List (List Sig))
def indexOf (ws : List Sig) (n : Nat) : Nat :=
  (ws.foldl (fun h w => h + (w.toNat % 65521)^2) 0) % n
def inLevel (db : Level) (ws : List Sig) : Bool :=
  match db[indexOf ws db.length]? with
  | none => false
  | some bucket => bucket.any fun old => decide (ws.toFinset=old.toFinset)
def Valid (cap : Nat) (db : Level) : Prop :=
  ∀ bucket∈db, ∀ ws∈bucket, ImpossibleM target cap ws.toFinset

theorem inLevel_sound {db : Level} {n : Nat} (valid : Valid n db) (ws : List Sig)
    (ok : inLevel db ws=true) : ImpossibleM target n ws.toFinset := by
  unfold inLevel at ok
  split at ok
  next => contradiction
  next bucket eq =>
    obtain ⟨old,hold,he⟩ := List.any_eq_true.mp ok
    rw [of_decide_eq_true he]
    exact valid _ (List.mem_of_getElem? eq) _ hold

def allParents (cap : Nat) (db : Level) (bucket : List (List Sig)) : Bool :=
  bucket.all fun ws => decide ws.Nodup && checks (inLevel db) cap ws

theorem step {cap : Nat} {next current : Level} (hv : Valid (cap-1) next)
    (ok : ∀ bucket∈current, allParents cap next bucket=true) : Valid cap current := by
  intro bucket hb ws hw
  obtain ⟨nd,yes⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (ok bucket hb) ws hw)
  exact node_sound cap ws (of_decide_eq_true nd) _ yes (inLevel_sound hv)
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
def pairRow (r : Row) : Fin 25 := ([1,1,1,3,4,4,4,5,5,5,7,9,9,9,14,19,20,20,20,21,21,21,0,6,24,0,0,6,24,0,6,24,6,0,6,24,24,24,0,6,24,0,6,24] : List (Fin 25)).getD r.val 0

def left (r : Row) := Fin.ofNat 5 ((pairRow r).val / 5)
def right (r : Row) := Fin.ofNat 5 (pairRow r).val
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem inputs_agree : ∀ r : Row, inputs.map (bit r) = PEqualNP.Represents.oneEach (left r) (right r) := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem outputs_agree : ∀ r : Row, (3687098 : Nat).testBit (5*(left r).val+(right r).val) = bit r target := by decide +kernel
def cuts : List (Sig × Row × Row) := [(2483132825727,1,23),(4970493525888,7,29),(16384,14,36),(32768,15,37),(10138559643648,16,38),(2483133285248,8,30),(4970497179655,0,22),(1024,10,32),(8,3,25),(10138555578480,4,26)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem essential : ∀ w∈inputs, ∃ r s : Row, bit r target=true ∧ bit s target=false ∧
    ∀ v∈inputs, bit r v=true → bit s v=false → v=w := by
  have cover : ∀ w∈inputs, ∃ q∈cuts, q.1=w := by decide +kernel
  have verified : ∀ q∈cuts, bit q.2.1 target=true ∧ bit q.2.2 target=false ∧
      ∀ v∈inputs, bit q.2.1 v=true → bit q.2.2 v=false → v=q.1 := by decide +kernel
  intro w hw
  obtain ⟨q,hq,rfl⟩ := cover w hw
  exact ⟨q.2.1,q.2.2,verified q hq⟩
theorem lower (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (correct : ∀ r : Row, C.eval (inputs.map (bit r)) = bit r target) (certificate : ImpossibleM target 10 inputs.toFinset) : 11≤C.size := by
  by_contra! small
  have weq : (execute C.gates inputs).getD C.output zero=target := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute C.gates inputs).getD C.output zero)=bit r target
    rw [←b_read,execute_bits _ _ _ (fun g hg => by
      have op : g.op=.and ∨ g.op=.or := by simpa using (hC g hg).1
      rcases op with e | e <;> simp [e])]
    exact correct r
  have rep := get_rep (execute C.gates inputs) C.output
  rw [weq] at rep
  have pro : proper target := by unfold proper; decide
  obtain ⟨k,S,hk,run,sub⟩ := extractM C.gates inputs hC pro (rep.resolve_right (fun n => n pro))

  have eq : inputs.toFinset=S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,sub a⟩
    obtain ⟨r,s,yes,no,only⟩ := essential a hm
    obtain ⟨v,hv,hp,hn⟩ := mono_row_difference run rfl yes no
    exact (only v (sub v hv) hp hn) ▸ hv
  exact certificate k 0 (by change k≤C.size at hk; omega) rfl (eq.symm ▸ run)

theorem goal_of (h : ImpossibleM target 10 inputs.toFinset) :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3687098 : Nat).testBit (5*u.val+v.val)) 10 := by
  rintro ⟨C,mono,size,rep⟩
  have lb := lower C mono (fun r => by
    rw [inputs_agree]
    exact (rep (left r) (right r)).trans (outputs_agree r)) h
  omega

namespace Minor
def inputs : List Sig := [10052681072703,2513168240576,5026336731136,10052677169600,2513170300935,5026338573880]
def cuts : List (Sig × Row × Row) := [(10052681072703,1,23),(2513168240576,6,28),(5026336731136,12,34),(10052677169600,7,29),(2513170300935,0,22),(5026338573880,3,25)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem essential : ∀ w∈inputs, ∃ r s : Row, bit r target=true ∧ bit s target=false ∧
    ∀ v∈inputs, bit r v=true → bit s v=false → v=w := by
  have cover : ∀ w∈inputs, ∃ q∈cuts, q.1=w := by decide +kernel
  have verified : ∀ q∈cuts, bit q.2.1 target=true ∧ bit q.2.2 target=false ∧
      ∀ v∈inputs, bit q.2.1 v=true → bit q.2.2 v=false → v=q.1 := by decide +kernel
  intro w hw
  obtain ⟨q,hq,rfl⟩ := cover w hw
  exact ⟨q.2.1,q.2.2,verified q hq⟩
def s0 : Sig := 2513168240576
def s1 : Sig := 2513170300935
def s2 : Sig := 2513170304967
def s3 : Sig := 5026336731136
def s4 : Sig := 5026338573880
def s5 : Sig := 5026338831928
def s6 : Sig := 10052677169600
def s7 : Sig := 10052681072703
def s8 : Sig := 10052681101823
def L2 : Level := []
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v2 : Valid 2 L2 := by simp [Valid,L2]
def B3 : List (List Sig) := [[s0,s2,s5,s8],[s1,s2,s5,s8],[s2,s3,s5,s8],[s2,s4,s5,s8],[s2,s5,s6,s8],[s2,s5,s7,s8],[s2,s5,s8]]
def L3 : Level := [B3]
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p3_0 : allParents 3 L2 B3=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v3 : Valid 3 L3 := by
  apply step (cap := 3) v2
  simpa only [L3,List.mem_singleton,forall_eq] using p3_0
def B4 : List (List Sig) := [[s0,s1,s3,s5,s8],[s0,s1,s4,s5,s8],[s0,s1,s5,s6,s8],[s0,s1,s5,s7,s8],[s0,s1,s5,s8],[s0,s2,s3,s4,s8],[s0,s2,s5,s6,s7],[s1,s2,s3,s4,s8],[s1,s2,s5,s6,s7],[s2,s3,s4,s6,s8],[s2,s3,s4,s7,s8],[s2,s3,s4,s8],[s2,s3,s5,s6,s7],[s2,s4,s5,s6,s7],[s2,s5,s6,s7]]
def L4 : Level := [B4]
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p4_0 : allParents 4 L3 B4=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v4 : Valid 4 L4 := by
  apply step (cap := 4) v3
  simpa only [L4,List.mem_singleton,forall_eq] using p4_0
def B5 : List (List Sig) := [[s0,s1,s3,s4,s6,s8],[s0,s1,s3,s4,s7,s8],[s0,s1,s3,s4,s8],[s0,s1,s3,s5,s6,s7],[s0,s1,s4,s5,s6,s7],[s0,s1,s5,s6,s7],[s0,s2,s3,s4,s6,s7],[s1,s2,s3,s4,s6,s7],[s2,s3,s4,s6,s7]]
def L5 : Level := [B5]
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p5_0 : allParents 5 L4 B5=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v5 : Valid 5 L5 := by
  apply step (cap := 5) v4
  simpa only [L5,List.mem_singleton,forall_eq] using p5_0
def B6 : List (List Sig) := [[s0,s1,s3,s4,s6,s7]]
def L6 : Level := [B6]
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_0 : allParents 6 L5 B6=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v6 : Valid 6 L6 := by
  apply step (cap := 6) v5
  simpa only [L6,List.mem_singleton,forall_eq] using p6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem certificate : ImpossibleM target 6 inputs.toFinset := by
  let ws := [s0,s1,s3,s4,s6,s7]
  have eq : inputs.toFinset=ws.toFinset := by dsimp only [ws]; decide
  rw [eq]
  exact v6 _ (by simp [L6]) ws (by simp [ws,B6])
end Minor
namespace Project
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
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
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

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (none : u=0) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | unary _ _ _ _ => omega
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
    have progress := ih none (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


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


theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k S} (run : Live T k 0 S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l U, l ≤ p+k ∧ Live T l 0 U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',S',hk,hk',hs⟩ := pull_gateM run (bin_repM d (available_rep ha) (available_rep hb))
      (fun x hx => by simpa [or_comm] using sub x hx)
    obtain ⟨l,U,hl,hr,hs⟩ := ih hk' hs
    exact ⟨l,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live T k 0 S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs
theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv


def focusData : List (Fin 44) := [0,1,2,4,5,6,7,8,9,11,12,13,16,17,18,19,20,21]
def focus (r : Row) : Row :=
  let v := (focusData.getD ((r.val % 22)%18) 0).val
  Fin.ofNat 44 (if r.val<22 then v else v+22)
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem keeps : restrictRows focus (observe target)=observe target := by
  funext r
  exact (by decide +kernel : ∀ i : Row, bit (focus i) target = bit i target) r
theorem zero_const : Constant (observe zero) := ⟨false,funext bit_zero⟩
def a0 : Sig := 2483132825727
def q0 : Sig := 10052681072703
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem proj0 : restrictRows focus (observe a0) = observe q0 := by
  funext r
  exact (by decide +kernel : ∀ i : Row, bit (focus i) a0 = bit i q0) r
def a1 : Sig := 4970493525888
def q1 : Sig := 2513168240576
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem proj1 : restrictRows focus (observe a1) = observe q1 := by
  funext r
  exact (by decide +kernel : ∀ i : Row, bit (focus i) a1 = bit i q1) r
def a2 : Sig := 16384
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem proj2 : restrictRows focus (observe a2) = observe zero := by
  funext r
  exact (by decide +kernel : ∀ i : Row, bit (focus i) a2 = bit i zero) r
def a3 : Sig := 32768
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem proj3 : restrictRows focus (observe a3) = observe zero := by
  funext r
  exact (by decide +kernel : ∀ i : Row, bit (focus i) a3 = bit i zero) r
def a4 : Sig := 10138559643648
def q4 : Sig := 5026336731136
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem proj4 : restrictRows focus (observe a4) = observe q4 := by
  funext r
  exact (by decide +kernel : ∀ i : Row, bit (focus i) a4 = bit i q4) r
def a5 : Sig := 2483133285248
def q5 : Sig := 10052677169600
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem proj5 : restrictRows focus (observe a5) = observe q5 := by
  funext r
  exact (by decide +kernel : ∀ i : Row, bit (focus i) a5 = bit i q5) r
def a6 : Sig := 4970497179655
def q6 : Sig := 2513170300935
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem proj6 : restrictRows focus (observe a6) = observe q6 := by
  funext r
  exact (by decide +kernel : ∀ i : Row, bit (focus i) a6 = bit i q6) r
def a7 : Sig := 1024
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem proj7 : restrictRows focus (observe a7) = observe zero := by
  funext r
  exact (by decide +kernel : ∀ i : Row, bit (focus i) a7 = bit i zero) r
def a8 : Sig := 8
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem proj8 : restrictRows focus (observe a8) = observe zero := by
  funext r
  exact (by decide +kernel : ∀ i : Row, bit (focus i) a8 = bit i zero) r
def a9 : Sig := 10138555578480
def q9 : Sig := 5026338573880
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem proj9 : restrictRows focus (observe a9) = observe q9 := by
  funext r
  exact (by decide +kernel : ∀ i : Row, bit (focus i) a9 = bit i q9) r
def mapped : List (Wire Row) := [observe q0,observe q1,observe zero,observe zero,observe q4,observe q5,observe q6,observe zero,observe zero,observe q9]
theorem restrict_inputs : (inputs.map observe).map (restrictRows focus) = mapped := by
  change [restrictRows focus (observe a0),restrictRows focus (observe a1),restrictRows focus (observe a2),restrictRows focus (observe a3),restrictRows focus (observe a4),restrictRows focus (observe a5),restrictRows focus (observe a6),restrictRows focus (observe a7),restrictRows focus (observe a8),restrictRows focus (observe a9)] = _
  rw [proj0,proj1,proj2,proj3,proj4,proj5,proj6,proj7,proj8,proj9]
  rfl
theorem covered : supply (Minor.inputs.map observe) mapped := by
  intro a ha
  change a ∈ [observe q0,observe q1,observe zero,observe zero,observe q4,observe q5,observe q6,observe zero,observe zero,observe q9] at ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply Or.inl
    apply List.mem_map_of_mem
    decide
  · apply Or.inl
    apply List.mem_map_of_mem
    decide
  · exact Or.inr zero_const
  · exact Or.inr zero_const
  · apply Or.inl
    apply List.mem_map_of_mem
    decide
  · apply Or.inl
    apply List.mem_map_of_mem
    decide
  · apply Or.inl
    apply List.mem_map_of_mem
    decide
  · exact Or.inr zero_const
  · exact Or.inr zero_const
  · apply Or.inl
    apply List.mem_map_of_mem
    decide
theorem charged : 4 ≤ mass mapped := by
  have z : cost (observe zero) = 1 := by simp [cost,zero_const]
  have empty : mass ([] : List (Wire Row)) = 0 := rfl
  simp only [mapped,mass_cons,z,empty]
  omega

theorem small_lower (q bank) (paid : Reach (Minor.inputs.map observe) q bank)
    (hit : Available bank (observe target)) : 7 ≤ q := by
  obtain ⟨k,S,hk,hr,hs⟩ := reach_live (by decide : proper target) paid hit
  have he : Minor.inputs.toFinset=S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,yes,no,only⟩ := Minor.essential a hm
    obtain ⟨v,hv,hp,hn⟩ := mono_row_difference hr rfl yes no
    exact (only v (hs v hv) hp hn) ▸ hv
  by_contra! small
  exact Minor.certificate k 0 (by omega) rfl (he.symm ▸ hr)

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem certificate : ImpossibleM target 10 inputs.toFinset := by
  intro k t hk ht run
  have start := list_run run ht inputs (by decide) rfl
  have cv : supply (Minor.inputs.map observe) ((inputs.map observe).map (restrictRows focus)) :=
    restrict_inputs.symm ▸ covered
  have nc : ¬Constant (restrictRows focus (observe target)) := by
    rw [keeps]
    exact observe_proper (by decide)
  have hbound := projected_bound focus start nc (Reach.start (roots:=Minor.inputs.map observe)) cv
    (L:=7) (by rw [keeps]; exact small_lower)
  rw [restrict_inputs] at hbound
  have h4 := charged
  omega
end Project
end PEqualNP.Outside.L_meta_9399
theorem PEqualNP.Outside.L_meta_9399 :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3687098 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_9399.goal_of PEqualNP.Outside.L_meta_9399.Project.certificate

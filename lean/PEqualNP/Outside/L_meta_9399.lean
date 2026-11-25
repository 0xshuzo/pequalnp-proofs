import PEqualNP.Defs

-- Live-frontier checking adapts the proof by PressF10 from pequalnp-proofs PR 4332.
namespace PEqualNP.Outside.L_meta_9399
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 300
def zero : Sig := 0
def one : Sig := BitVec.allOnes 300
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

def bit (i : Fin 300) (a : Sig) : Bool := a.getLsbD i.val
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

abbrev Row := Fin 300
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

def target : Sig := 1427247692705959881058285969449495136382746623
def inputs : List Sig := [186501905240133617932839047371689031133591881365888414373929310125683950074599781171199,746007620960534471731356189486756124534367525463553657495718478442775085502752163364864,14920152419210689434627123789735122490687350509271073149954908391321980058620852330037248,238722438707371030954033980635761959850997608148337171727816947926584025613410889403203584,1782460875681703697790120388747022633554115475601498563686498945247906835055727612505620480,16971673376852159231888353310823701833156861204339400521765451559844679652417328511975424,34067681357197740875731932653228529687069451756706420255298421584587592373610418110758911,322399626858444314199901099889859771819602498921165772314399134103970099413744223055249408,645047922923875473223712651842881795680716453684152729181296840621365555202991429286592512,1018549071818116398737211650712584362030923128099571928363380601484613373120573307218821120]
def column (w : Sig) := w &&& ~~~(w >>> 150)
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
  · have geom : ∀ r : Fin 300,bit r target=true →
        r.val+150<300 ∧ bit (Fin.ofNat 300 (r.val+150)) target=false := by decide +kernel
    obtain ⟨hv,hn⟩ := geom ⟨i,hi⟩ p
    obtain ⟨v,hm,hp,hh⟩ := mono_row_difference (r := ⟨i,hi⟩) (s := Fin.ofNat 300 (i+150)) z none p hn
    have hn' : v.getLsbD (i+150)=false := by
      change v.getLsbD ((i+150)%300)=false at hh
      rwa [Nat.mod_eq_of_lt hv] at hh
    have col : (column v).getLsbD i=true := by
      change v.getLsbD i=true at hp
      simp [column,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_not,hi,hp,hn',Nat.add_comm 150 i]
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
def pairRow (r : Row) : Fin 25 := ([1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,14,14,14,14,14,14,14,14,14,14,14,14,14,14,14,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,0,2,6,8,10,11,12,13,15,16,17,18,22,23,24,0,2,6,8,10,11,12,13,15,16,17,18,22,23,24,0,2,6,8,10,11,12,13,15,16,17,18,22,23,24,0,2,6,8,10,11,12,13,15,16,17,18,22,23,24,0,2,6,8,10,11,12,13,15,16,17,18,22,23,24,0,2,6,8,10,11,12,13,15,16,17,18,22,23,24,0,2,6,8,10,11,12,13,15,16,17,18,22,23,24,0,2,6,8,10,11,12,13,15,16,17,18,22,23,24,0,2,6,8,10,11,12,13,15,16,17,18,22,23,24,0,2,6,8,10,11,12,13,15,16,17,18,22,23,24] : List (Fin 25)).getD r.val 0

def left (r : Row) := Fin.ofNat 5 ((pairRow r).val / 5)
def right (r : Row) := Fin.ofNat 5 (pairRow r).val
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem inputs_agree : ∀ r : Row, inputs.map (bit r) = PEqualNP.Represents.oneEach (left r) (right r) := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem outputs_agree : ∀ r : Row, (3687098 : Nat).testBit (5*(left r).val+(right r).val) = bit r target := by decide +kernel
def cuts : List (Sig × Row × Row) := [(186501905240133617932839047371689031133591881365888414373929310125683950074599781171199,2,152),(746007620960534471731356189486756124534367525463553657495718478442775085502752163364864,45,195),(14920152419210689434627123789735122490687350509271073149954908391321980058620852330037248,104,254),(238722438707371030954033980635761959850997608148337171727816947926584025613410889403203584,119,269),(1782460875681703697790120388747022633554115475601498563686498945247906835055727612505620480,120,270),(16971673376852159231888353310823701833156861204339400521765451559844679652417328511975424,47,197),(34067681357197740875731932653228529687069451756706420255298421584587592373610418110758911,0,150),(322399626858444314199901099889859771819602498921165772314399134103970099413744223055249408,62,212),(645047922923875473223712651842881795680716453684152729181296840621365555202991429286592512,15,165),(1018549071818116398737211650712584362030923128099571928363380601484613373120573307218821120,30,180)]

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
def s0 : Sig := 1073709056
def s1 : Sig := 37777778941452554862592
def s2 : Sig := 40563581267264055467619603447808
def s3 : Sig := 1329187430965708569562959165777772544
def s4 : Sig := 1329227994546975833618426785381220352
def s5 : Sig := 186501905240133617932839047371689031133591881365888414373929310125683950074599781171199
def s6 : Sig := 186501905240133617932839047371689031133591881365888414373929310163461729016052336033791
def s7 : Sig := 186501905240133617932839047371689031133591881365888414414492891392948005542219384619007
def s8 : Sig := 186501905240133617932839047371689031133591881365889743561360275834253513033765558943743
def s9 : Sig := 186501905240133617932839047371689031133591881365889743601923857101517568501385162391551
def s10 : Sig := 746007620960534471731356189486756124534367525463553657495718478442775085502752163364864
def s11 : Sig := 746007620960534471731356189486756124534367525463553657495718478442775085502753237073920
def s12 : Sig := 746007620960534471731356189486756124534367525463553657536282059710039140970371766812672
def s13 : Sig := 746007620960534471731356189486756124534367525463554986683149444151344648461917941137408
def s14 : Sig := 746007620960534471731356189486756124534367525463554986723713025418608703929537544585216
def s15 : Sig := 14920152419210689434627123789735122490687350509271073149954908391321980058620852330037248
def s16 : Sig := 14920152419210689434627123789735122490687350509271073149954908391321980058620853403746304
def s17 : Sig := 14920152419210689434627123789735122490687350509271073149954908391359757837562304884899840
def s18 : Sig := 14920152419210689434627123789735122490687350509271074479142339357030549621580018107809792
def s19 : Sig := 15106654324450823052559962837106811521820942390636961564328837701447664008695452111208447
def s20 : Sig := 15666160040171223906358479979221878615221718034734626807450626869764755144123604493402112
def s21 : Sig := 16971673376852159231888353310823701833156861204339400521765451559844679652417328511975424
def s22 : Sig := 16971673376852159231888353310823701833156861204339400521765451559882457431358781066838016
def s23 : Sig := 16971673376852159231888353310823701833156861204339400521806015141111943707884948115423232
def s24 : Sig := 16971673376852159231888353310823701833156861204339401850952882525553249215376494289747968
def s25 : Sig := 16971673376852159231888353310823701833156861204339401850993446106820513270844113893195776
def s26 : Sig := 17096007980345581643843579342404827853912589125249992798014737766595135619145456490119167
def s27 : Sig := 17096007980345581643843579342404827853912589125249992798014737766632913398086909044981759
def s28 : Sig := 17096007980345581643843579342404827853912589125249992798055301347862399674613076093566975
def s29 : Sig := 17096007980345581643843579342404827853912589125249994127202168732303705182104622267891711
def s30 : Sig := 17096007980345581643843579342404827853912589125249994127242732313570969237572241871339519
def s31 : Sig := 30897148968115469370873668847909816157798388346325735461726070297163011977494631993573376
def s32 : Sig := 30897148968115469370873668847909816157798388346325735461726070297200789756436084548435968
def s33 : Sig := 30897148968115469370873668847909816157798388346325736790913501262871581540453797771345920
def s34 : Sig := 31021483571608891782828894879490942178554116267236327737975356503913467944222759971717119
def s35 : Sig := 34067681357197740875731932653228529687069451756706420255298421584587592373610418110758911
def s36 : Sig := 34067681357197740875731932653228529687069451756706420255298421584587592373610419184467967
def s37 : Sig := 34067681357197740875731932653228529687069451756706420255338985165854856429078037714206719
def s38 : Sig := 34067681357197740875731932653228529687069451756706421584485852550296161936569583888531455
def s39 : Sig := 34067681357197740875731932653228529687069451756706421584526416131563425992037203491979263
def s40 : Sig := 34565019771171430523552836779553033770092363440348789360295567649529455525727283062013951
def s41 : Sig := 34565019771171430523552836779553033770092363440348789360295567649529455525727284135723007
def s42 : Sig := 34565019771171430523552836779553033770092363440348789360336131230796719581194902665461759
def s43 : Sig := 34565019771171430523552836779553033770092363440348790689482998615238025088686448839786495
def s44 : Sig := 34565019771171430523552836779553033770092363440348790689523562196505289144154068443234303
def s45 : Sig := 46998480120513671719075439937665635845665155531408016985264750667902276965144172743917567
def s46 : Sig := 46998480120513671719075439937665635845665155531408016985264750667902276965144173817626623
def s47 : Sig := 46998480120513671719075439937665635845665155531408018314452181633610846528103338521690111
def s48 : Sig := 47495818534487361366896344063990139928688067215050386090261896732844140117261037695172607
def s49 : Sig := 238722438707371030954033980635761959850997608148337171727816947926584025613410889403203584
def s50 : Sig := 238722438707371030954033980635761959850997608148337171727816947926584025613410890476912640
def s51 : Sig := 238722438707371030954033980635761959850997608148337171727816947926621803392352341958066176
def s52 : Sig := 238722438707371030954033980635761959850997608148337171727857511507851289668878509006651392
def s53 : Sig := 238908940612611164571966819683133648882131200029703060142190877236709709563485489184374783
def s54 : Sig := 239468446328331565425765336825248715975531975673800725385312666405026800698913641566568448
def s55 : Sig := 239779282837065121455653401904201531027421295476120760889673765022370341529131436340150272
def s56 : Sig := 239779282837065121455653401904201531027421295476120760889673765022408119308072888895012864
def s57 : Sig := 239779282837065121455653401904201531027421295476120760889714328603637605584599055943598080
def s58 : Sig := 239903617440558543867608627935782657048177023397031353165923051229120797495859564318294015
def s59 : Sig := 240960461570252634369228049204222228224600712151931969263298100583054890513627744363905023
def s60 : Sig := 240960461570252634369228049204222228224600712151931969263298100583054890513627745437614079
def s61 : Sig := 240960461570252634369228049204222228224600712151931969263338664164322154569095363967352831
def s62 : Sig := 241457799984226324017048953330546732307623623835574338368295246647996753665744609315160063
def s63 : Sig := 253642591126581720388661104425497082341684958657608244877771856317906005672031741733240832
def s64 : Sig := 253642591126581720388661104425497082341684958657608244877771856317906005672031742806949888
def s65 : Sig := 253642591126581720388661104425497082341684958657608244877771856317943783450973194288103424
def s66 : Sig := 253704758428328431594638717441287645352062822618107095829634383759688673854208739821748224
def s67 : Sig := 253704758428328431594638717441287645352062822618107095829634383759726451633150192376610816
def s68 : Sig := 253829093031821854006593943472868771372818550538974133292145785628031689622106341514412031
def s69 : Sig := 253829093031821854006593943472868771372818550539017688105883669966439129820936867799891967
def s70 : Sig := 253891260333568565212571556488659334383196415926633565993264429666369575105161498997063679
def s71 : Sig := 253891260333568565212571556488659334383196415926633565993264429666369575105161500070772735
def s72 : Sig := 254388598747542254860392460614983838466219326183071798535267574796348780757534493896605696
def s73 : Sig := 254388598747542254860392460614983838466219327610275935098261575731311438257278363948318719
def s74 : Sig := 322399626858444314199901099889859771819602498921165772314399134103970099413744223055249408
def s75 : Sig := 322399626858444314199901099889859771819602498921165772314439697685237363469211842658697216
def s76 : Sig := 322399626858444314199901099889859771819602498921165773643586565069678668976703388833021952
def s77 : Sig := 322399626858444314199901099889859771819602498921165773643627128650945933032171008436469760
def s78 : Sig := 322461794160191025405878712905650334829980362881621068452523777207345327397125879230365695
def s79 : Sig := 322461794160191025405878712905650334829980362881621068452564340788612591452593498833813503
def s80 : Sig := 322461794160191025405878712905650334829980362881621069781711208173053896960085045008138239
def s81 : Sig := 322461794160191025405878712905650334829980362881621069781751771754321161015552664611586047
def s82 : Sig := 333341071965865486451960990668998861646106555961297892624376883879277488538190879991529472
def s83 : Sig := 333341071965865486451960990668998861646106555961297893953564314844986058101150045769302016
def s84 : Sig := 333403239267612197657938603684789424656484419921753188762501526982652716521572536166645759
def s85 : Sig := 339371300235296473431789453200683473652759360125505172836164585663814779066161551567224832
def s86 : Sig := 339371300235296473431789453200683473652759360125505172836164585663814779066196735939313663
def s87 : Sig := 349318068514770266388207535727173555313217593798352554936148045785118520457064659655065600
def s88 : Sig := 349318068514770266388207535727173555313217593798352554936148045785118520457099844027154431
def s89 : Sig := 497462748577183070232859352356085209043667411563279698602581544174320670080367986158338048
def s90 : Sig := 497462748577183070232859352356085209043667411563279698602622107755587934135835605761785856
def s91 : Sig := 497524915878929781438836965371875772054045275523734994740706187277695898063749642333454335
def s92 : Sig := 498519592706877160734478773624524780220091098891063287764438361270106985996088533095284736
def s93 : Sig := 498519592706877160734478773624524780220091098891063287764438361270106985996123717467373567
def s94 : Sig := 508404193684604242484919243135224298870171468603411818912559293949628059204814643094618112
def s95 : Sig := 508466360986350953690896856151014861880549332563867115050683937053003287188196299269734399
def s96 : Sig := 508466360986350953690896856151014861880549332563910669864421821391410727386991641183125504
def s97 : Sig := 508466360986350953690896856151014861880549332563910669864421821391410727387026825555214335
def s98 : Sig := 645047922923875473223712651842881795680716453684152729181296840621365555202991429286592512
def s99 : Sig := 645047922923875473223712651842881795680716453684152729181337404202632819258459048890040320
def s100 : Sig := 645047922923875473223712651842881795680716453684152730510484271587074124765950595064365056
def s101 : Sig := 645047922923875473223712651842881795680716453684152730510524835168341388821418214667812864
def s102 : Sig := 645296592130862318047623103906044047722227909525973913733795414272806506421722407025737728
def s103 : Sig := 645296592130862318047623103906044047722227909525973913733835977854073770477190026629185536
def s104 : Sig := 645296592130862318047623103906044047722227909525973915062982845238515075984681572803510272
def s105 : Sig := 645296592130862318047623103906044047722227909525973915063023408819782340040149192406958080
def s106 : Sig := 652010660719507128293205309611424852843037217255145896651297431780658353393263890829115392
def s107 : Sig := 652010660719507128293205309611424852843037217255145897980484862746366922956223056606887936
def s108 : Sig := 652259329926493973117115761674587104884548673096967081203796005432099304611994868568260608
def s109 : Sig := 679115604281073214099444584496110325367785905440859149436595262205953147576601847397351423
def s110 : Sig := 679115604281073214099444584496110325367785905440859149436595263443893186861946937924386815
def s111 : Sig := 684088988420810110577653625759355366198015022277282840486607274057238650299787211242995711
def s112 : Sig := 684088988420810110577653625759355366198015022277282840486607275295178689585132301770031103
def s113 : Sig := 756451727653981954335595176139570710277848670820043410029844712835482670922828066089566208
def s114 : Sig := 756451727653981954335595176139570710277848670820043410029885276416749934978295685693014016
def s115 : Sig := 756700396860968799159505628202732962319360126661864594582343286486923622141559043828711424
def s116 : Sig := 758689750516863557750789244708030978651451774823638207565325865491953535823044921050267647
def s117 : Sig := 758689750516863557750789244708030978651451774823638207565325866729893575108390011577303039
def s118 : Sig := 763414465449613609405087833908113767440169434391036577499845303994775469113100527632089088
def s119 : Sig := 763663134656600454228998285971276019481680890232857762052343877646216420331831505371234304
def s120 : Sig := 763663134656600454228998285971276019481680891660061898615337877343239038546230284895911935
def s121 : Sig := 763663134656600454228998285971276019481680891660061898615337878581179077831575375422947327
def s122 : Sig := 1018549071818116398737211650712584362030923128099571928363380601484613373120573307218821120
def s123 : Sig := 1018549071818116398737211650712584362030923128099571928363380601484613373120573308292530176
def s124 : Sig := 1018549071818116398737211650712584362030923128099571928363380601484651150899514759773683712
def s125 : Sig := 1340948698676560712937112750602444133850525627020737700677779735588583472534317530274070528
def s126 : Sig := 1663596994741991871960924302555466157711639581783724657544677442105978928323564736505413632
def s127 : Sig := 1782460875681703697790120388747022633554115475601498563686498945247906835055727612505620480
def s128 : Sig := 1782460875681703697790120388747022633554115475601498563686498945247906835055727613579329536
def s129 : Sig := 1782460875681703697790120388747022633554115475601498563686498945247944612834669065060483072
def s130 : Sig := 1782460875681703697790120388747022633554115475601498565015726941032784929027706898922602496
def s131 : Sig := 1782460875681703697790120388747022633554115475601498565015726941032784929027706899996311552
def s132 : Sig := 1782460875681703697790120388747022633554115475601498565015726941032822706806648351477465088
def s133 : Sig := 1850223234585618912305718575958736314865987192497771354242359927926943114682323330360410112
def s134 : Sig := 1850223234585618912305718575958736314865987192497771355571587923711821208654302616777392128
def s135 : Sig := 1918234262696520971645227215233612248219370365235865329350719483019404750684422031391293440
def s136 : Sig := 1918234262696520971645227215233612248219370365235865330679947478804282844656401317808275456
def L3 : Level := []
def B4_0 : List (List Sig) := [[s26,s40,s63,s74,s131],[s26,s40,s63,s98,s132],[s26,s40,s63,s134,s136],[s26,s41,s63,s74,s130],[s26,s44,s74,s98,s130],[s26,s73,s74,s110,s130],[s27,s40,s63,s98,s130],[s30,s40,s74,s98,s130],[s40,s69,s86,s98,s130]]
def L4 : Level := [B4_0]
def B5_0 : List (List Sig) := [[s5,s10,s21,s70,s98,s132],[s5,s10,s22,s70,s98,s130],[s5,s10,s31,s59,s98,s132],[s5,s10,s32,s59,s98,s130],[s5,s11,s35,s66,s74,s130],[s5,s21,s40,s107,s122,s133],[s5,s21,s40,s118,s125,s130],[s5,s21,s73,s74,s102,s130],[s11,s26,s35,s94,s122,s127],[s12,s26,s35,s89,s122,s135],[s15,s26,s41,s49,s74,s130],[s26,s35,s63,s102,s124,s127],[s26,s40,s66,s98,s122,s133],[s26,s40,s77,s98,s122,s127],[s28,s40,s49,s74,s98,s130],[s30,s35,s74,s102,s122,s127]]
def B5_1 : List (List Sig) := [[s5,s21,s40,s63,s126,s134],[s5,s21,s41,s63,s122,s133],[s5,s21,s42,s113,s122,s133],[s5,s25,s40,s98,s122,s133],[s10,s26,s35,s77,s122,s135],[s10,s26,s35,s96,s122,s135],[s10,s34,s59,s78,s98,s130],[s15,s26,s40,s49,s134,s136],[s26,s40,s63,s74,s109,s130],[s26,s40,s63,s85,s98,s130],[s26,s40,s63,s98,s125,s130],[s35,s69,s86,s102,s122,s127]]
def B5_2 : List (List Sig) := [[s5,s10,s21,s70,s74,s131],[s5,s10,s31,s59,s74,s131],[s5,s10,s35,s66,s98,s132],[s5,s31,s62,s74,s102,s130],[s6,s21,s70,s102,s122,s127],[s10,s26,s70,s78,s98,s130],[s10,s29,s35,s82,s122,s135],[s10,s45,s58,s78,s98,s130],[s21,s40,s81,s98,s122,s127],[s21,s44,s78,s98,s122,s127],[s26,s40,s63,s125,s126,s127],[s26,s40,s74,s101,s122,s127]]
def B5_3 : List (List Sig) := [[s0,s26,s40,s63,s74,s130],[s4,s26,s40,s74,s98,s130],[s5,s10,s45,s55,s134,s136],[s5,s21,s40,s64,s74,s130],[s5,s21,s40,s118,s122,s129],[s5,s21,s40,s118,s122,s133],[s6,s10,s45,s55,s98,s130],[s8,s21,s40,s106,s122,s133],[s10,s26,s35,s63,s134,s136],[s10,s26,s35,s90,s122,s135],[s10,s26,s35,s94,s122,s135],[s21,s73,s78,s110,s122,s127],[s26,s40,s63,s74,s122,s128],[s26,s40,s63,s74,s130,s136],[s26,s40,s73,s74,s98,s130]]
def B5_4 : List (List Sig) := [[s1,s26,s40,s63,s98,s130],[s5,s10,s35,s66,s74,s131],[s5,s10,s36,s66,s74,s130],[s5,s21,s43,s106,s122,s133],[s5,s21,s44,s98,s122,s133],[s5,s21,s62,s112,s122,s133],[s10,s26,s35,s94,s123,s127],[s10,s26,s35,s94,s126,s130],[s10,s26,s36,s94,s122,s127],[s10,s26,s39,s74,s98,s130],[s15,s26,s43,s74,s98,s130],[s15,s27,s40,s49,s98,s130],[s25,s35,s78,s102,s122,s127],[s26,s40,s63,s98,s122,s129],[s26,s40,s63,s98,s130,s133]]
def B5_5 : List (List Sig) := [[s5,s10,s21,s71,s74,s130],[s5,s10,s35,s67,s98,s130],[s5,s21,s73,s110,s122,s133],[s5,s23,s40,s113,s122,s133],[s6,s21,s40,s118,s122,s127],[s10,s26,s35,s63,s125,s136],[s10,s26,s38,s82,s122,s135],[s10,s26,s70,s74,s109,s130],[s21,s40,s68,s78,s98,s130],[s26,s35,s77,s102,s122,s127],[s26,s40,s66,s74,s98,s130],[s26,s41,s63,s74,s122,s127]]
def B5_6 : List (List Sig) := [[s5,s21,s41,s63,s74,s130],[s5,s21,s48,s117,s122,s133],[s5,s25,s40,s74,s98,s130],[s5,s40,s66,s74,s102,s130],[s10,s26,s37,s89,s122,s135],[s10,s27,s35,s63,s98,s130],[s21,s39,s78,s102,s122,s127],[s26,s35,s63,s102,s125,s130],[s26,s40,s52,s74,s98,s130],[s26,s40,s63,s74,s110,s130],[s26,s40,s94,s102,s122,s127],[s34,s40,s49,s86,s98,s130]]
def B5_7 : List (List Sig) := [[s5,s11,s45,s55,s74,s130],[s5,s21,s40,s63,s134,s136],[s5,s21,s40,s119,s122,s133],[s6,s21,s40,s63,s98,s130],[s10,s26,s35,s95,s122,s135],[s10,s26,s35,s97,s122,s135],[s11,s26,s35,s63,s74,s130],[s15,s26,s40,s49,s98,s132],[s21,s35,s78,s105,s122,s127],[s21,s35,s81,s102,s122,s127],[s26,s48,s49,s74,s110,s130],[s34,s40,s58,s74,s98,s130]]
def B5_8 : List (List Sig) := [[s5,s21,s40,s120,s122,s133],[s5,s21,s70,s102,s124,s127],[s5,s22,s70,s102,s122,s127],[s5,s24,s40,s106,s122,s133],[s7,s21,s40,s113,s122,s133],[s9,s21,s40,s98,s122,s133],[s10,s26,s35,s65,s98,s130],[s10,s26,s39,s74,s122,s135],[s21,s40,s63,s78,s123,s127],[s21,s40,s63,s78,s126,s130],[s21,s70,s78,s110,s122,s127],[s26,s40,s63,s122,s133,s135],[s26,s40,s69,s74,s98,s130],[s26,s40,s70,s74,s98,s130],[s26,s44,s74,s98,s122,s127]]
def B5_9 : List (List Sig) := [[s5,s10,s45,s55,s98,s132],[s5,s21,s44,s74,s98,s130],[s10,s26,s35,s63,s98,s132],[s10,s30,s35,s74,s98,s130],[s14,s26,s35,s74,s98,s130],[s15,s26,s40,s49,s74,s131],[s18,s26,s40,s74,s98,s130],[s26,s73,s74,s110,s122,s127],[s27,s40,s63,s98,s122,s127]]
def B5_10 : List (List Sig) := [[s5,s21,s40,s63,s123,s133],[s5,s21,s73,s74,s110,s130],[s10,s26,s35,s94,s122,s128],[s10,s26,s35,s94,s122,s136],[s10,s27,s35,s63,s122,s135],[s10,s35,s69,s86,s98,s130],[s11,s35,s66,s78,s122,s127],[s26,s70,s78,s102,s122,s127],[s40,s66,s86,s98,s122,s127]]
def B5_11 : List (List Sig) := [[s5,s10,s21,s70,s134,s136],[s5,s10,s31,s59,s134,s136],[s5,s10,s31,s60,s74,s130],[s5,s10,s45,s55,s74,s131],[s5,s21,s40,s118,s124,s127],[s5,s22,s40,s118,s122,s127],[s5,s40,s66,s85,s98,s130],[s6,s10,s21,s70,s98,s130],[s6,s10,s31,s59,s98,s130],[s10,s26,s35,s63,s74,s131],[s10,s26,s36,s63,s74,s130],[s13,s26,s35,s82,s122,s135],[s15,s29,s40,s74,s98,s130],[s26,s40,s68,s74,s98,s130],[s26,s40,s72,s74,s98,s130]]
def B5_12 : List (List Sig) := [[s5,s10,s45,s56,s98,s130],[s5,s10,s46,s55,s74,s130],[s5,s21,s40,s121,s122,s133],[s10,s26,s35,s65,s122,s135],[s10,s35,s69,s78,s98,s130],[s15,s26,s62,s74,s110,s130],[s26,s39,s74,s102,s122,s127],[s26,s40,s63,s98,s124,s127],[s26,s40,s70,s74,s122,s135],[s26,s48,s62,s74,s98,s130],[s30,s40,s74,s98,s122,s127]]
def B5_13 : List (List Sig) := [[s5,s10,s35,s66,s134,s136],[s5,s21,s40,s63,s98,s132],[s5,s22,s40,s63,s98,s130],[s5,s48,s55,s74,s102,s130],[s6,s10,s35,s66,s98,s130],[s9,s21,s40,s74,s98,s130],[s10,s26,s35,s63,s124,s135],[s10,s30,s35,s74,s122,s135],[s10,s34,s35,s93,s122,s135],[s14,s26,s35,s74,s122,s135],[s21,s40,s78,s101,s122,s127],[s26,s35,s74,s105,s122,s127],[s26,s40,s63,s74,s102,s130],[s26,s40,s63,s74,s130,s135],[s26,s40,s63,s86,s98,s130],[s26,s40,s78,s118,s122,s127],[s26,s42,s49,s74,s98,s130],[s40,s69,s86,s98,s122,s127]]
def B5_14 : List (List Sig) := [[s5,s21,s40,s114,s122,s133],[s5,s21,s70,s102,s125,s130],[s10,s26,s35,s83,s122,s135],[s10,s28,s35,s89,s122,s135],[s10,s35,s66,s78,s123,s127],[s10,s35,s66,s78,s126,s130],[s10,s35,s69,s86,s122,s135],[s10,s36,s66,s78,s122,s127],[s15,s40,s58,s86,s98,s130],[s26,s40,s63,s74,s123,s127],[s26,s40,s63,s74,s126,s130],[s26,s70,s74,s110,s122,s127],[s27,s35,s63,s102,s122,s127]]
def B5_15 : List (List Sig) := [[s5,s11,s21,s70,s74,s130],[s5,s11,s31,s59,s74,s130],[s5,s21,s40,s63,s74,s131],[s5,s21,s40,s64,s122,s133],[s5,s21,s40,s101,s122,s133],[s5,s21,s40,s118,s122,s134],[s26,s40,s63,s78,s98,s130],[s35,s66,s86,s102,s122,s127]]
def B5_16 : List (List Sig) := [[s10,s35,s58,s88,s122,s135],[s21,s41,s63,s78,s122,s127],[s25,s40,s78,s98,s122,s127],[s26,s35,s72,s74,s102,s130],[s26,s40,s63,s98,s130,s134],[s40,s66,s78,s102,s122,s127]]
def L5 : Level := [B5_0,B5_1,B5_2,B5_3,B5_4,B5_5,B5_6,B5_7,B5_8,B5_9,B5_10,B5_11,B5_12,B5_13,B5_14,B5_15,B5_16]
def B6_0 : List (List Sig) := [[s5,s10,s15,s21,s59,s134,s136],[s5,s10,s21,s35,s90,s122,s135],[s5,s10,s21,s39,s74,s98,s130],[s5,s10,s21,s45,s49,s74,s131],[s5,s10,s21,s70,s74,s118,s130],[s5,s10,s48,s55,s74,s98,s130],[s5,s21,s45,s49,s102,s125,s130],[s10,s21,s35,s81,s98,s122,s127],[s10,s26,s38,s82,s98,s122,s127],[s20,s26,s35,s54,s74,s122,s135],[s21,s40,s73,s78,s98,s122,s127]]
def B6_1 : List (List Sig) := [[s5,s10,s15,s22,s59,s98,s130],[s5,s10,s21,s45,s89,s123,s127],[s5,s10,s31,s59,s74,s113,s130],[s5,s21,s40,s63,s98,s130,s134],[s6,s10,s15,s21,s59,s98,s130],[s10,s15,s26,s59,s78,s98,s130],[s10,s26,s35,s49,s87,s122,s135],[s10,s26,s35,s66,s74,s98,s130],[s10,s28,s35,s49,s74,s98,s130],[s10,s31,s35,s49,s78,s123,s127],[s15,s21,s35,s78,s104,s122,s127],[s19,s26,s40,s49,s74,s98,s130]]
def B6_2 : List (List Sig) := [[s3,s15,s26,s40,s74,s98,s130],[s5,s10,s16,s35,s55,s74,s130],[s5,s10,s21,s70,s78,s98,s130],[s5,s21,s40,s49,s106,s124,s127],[s5,s21,s48,s89,s102,s122,s127],[s5,s21,s59,s74,s103,s122,s127],[s5,s40,s66,s85,s98,s122,s127],[s10,s15,s26,s35,s49,s74,s131],[s10,s15,s26,s38,s74,s98,s130],[s10,s21,s35,s63,s78,s126,s130],[s10,s21,s35,s68,s78,s98,s130],[s10,s26,s35,s74,s94,s122,s135],[s10,s26,s35,s77,s98,s122,s127],[s10,s26,s39,s74,s98,s122,s127],[s15,s26,s35,s49,s102,s125,s130]]
def B6_3 : List (List Sig) := [[s0,s10,s26,s35,s63,s74,s130],[s5,s10,s21,s45,s89,s122,s128],[s5,s15,s21,s40,s113,s122,s129],[s10,s15,s26,s35,s89,s123,s127],[s10,s15,s26,s35,s91,s122,s135],[s10,s26,s35,s63,s89,s98,s130],[s10,s26,s35,s72,s74,s98,s130],[s10,s30,s35,s74,s98,s122,s127],[s15,s40,s55,s86,s98,s122,s127],[s21,s40,s78,s94,s98,s122,s127],[s26,s40,s63,s86,s98,s122,s127]]
def B6_4 : List (List Sig) := [[s5,s10,s21,s45,s49,s134,s136],[s5,s10,s21,s70,s74,s102,s130],[s5,s10,s21,s70,s98,s130,s133],[s5,s10,s22,s70,s98,s122,s127],[s5,s10,s31,s35,s49,s98,s132],[s5,s10,s35,s55,s87,s122,s135],[s5,s15,s21,s40,s116,s122,s133],[s5,s18,s21,s40,s74,s98,s130],[s5,s21,s40,s63,s122,s126,s133],[s5,s21,s40,s68,s98,s122,s133],[s5,s26,s40,s63,s74,s98,s130],[s5,s31,s35,s54,s74,s102,s130],[s6,s10,s21,s70,s98,s122,s127],[s10,s26,s59,s84,s98,s122,s127],[s10,s26,s70,s78,s98,s122,s127],[s12,s26,s35,s49,s74,s122,s135],[s15,s21,s40,s49,s78,s126,s130],[s21,s26,s40,s63,s74,s98,s130]]
def B6_5 : List (List Sig) := [[s0,s15,s26,s40,s49,s74,s130],[s5,s10,s15,s35,s55,s74,s131],[s5,s10,s21,s70,s74,s116,s130],[s5,s10,s21,s70,s125,s126,s127],[s5,s10,s22,s45,s49,s98,s130],[s5,s21,s40,s49,s99,s122,s133],[s5,s45,s55,s85,s102,s122,s127],[s6,s10,s21,s45,s49,s98,s130],[s10,s15,s26,s35,s89,s122,s128],[s10,s26,s45,s49,s78,s98,s130],[s10,s31,s35,s78,s100,s122,s127]]
def B6_6 : List (List Sig) := [[s5,s10,s21,s35,s63,s125,s136],[s5,s10,s21,s35,s118,s125,s130],[s5,s10,s31,s59,s98,s130,s134],[s5,s11,s35,s66,s74,s122,s127],[s5,s15,s21,s62,s110,s122,s133],[s5,s21,s40,s55,s106,s122,s133],[s5,s21,s40,s63,s109,s122,s133],[s6,s10,s35,s55,s106,s122,s127],[s10,s15,s26,s35,s49,s134,s136],[s10,s26,s35,s63,s98,s124,s127],[s10,s26,s35,s89,s94,s122,s135],[s10,s35,s66,s86,s98,s122,s127],[s15,s21,s59,s78,s110,s122,s127],[s18,s26,s40,s74,s98,s122,s127],[s20,s26,s35,s89,s102,s122,s127]]
def B6_7 : List (List Sig) := [[s5,s10,s21,s35,s94,s118,s130],[s5,s10,s21,s59,s82,s106,s130],[s5,s10,s35,s66,s74,s98,s130],[s5,s10,s40,s66,s74,s98,s130],[s5,s10,s45,s55,s92,s98,s130],[s10,s19,s21,s59,s78,s98,s130],[s10,s35,s55,s79,s98,s122,s127]]
def B6_8 : List (List Sig) := [[s5,s10,s21,s45,s113,s125,s130],[s5,s10,s45,s55,s78,s98,s130],[s5,s15,s21,s40,s50,s74,s130],[s5,s15,s21,s41,s49,s74,s130],[s5,s21,s40,s48,s113,s122,s133],[s5,s21,s40,s74,s119,s122,s127],[s5,s21,s48,s49,s110,s122,s133],[s10,s35,s55,s78,s99,s122,s127],[s15,s26,s40,s49,s98,s124,s127],[s26,s35,s49,s74,s103,s122,s127]]
def B6_9 : List (List Sig) := [[s5,s10,s15,s35,s55,s134,s136],[s5,s10,s21,s35,s119,s122,s133],[s5,s10,s35,s67,s98,s122,s127],[s10,s19,s21,s35,s91,s122,s135],[s10,s20,s26,s35,s89,s122,s135],[s10,s37,s55,s78,s98,s122,s127],[s21,s40,s63,s86,s98,s122,s127]]
def B6_10 : List (List Sig) := [[s3,s5,s21,s40,s106,s122,s133],[s4,s5,s21,s40,s74,s98,s130],[s5,s10,s21,s35,s118,s122,s134],[s5,s10,s21,s38,s106,s122,s133],[s5,s10,s24,s45,s74,s98,s130],[s5,s10,s45,s55,s74,s102,s130],[s5,s10,s45,s55,s98,s130,s133],[s5,s11,s21,s35,s63,s122,s133],[s5,s16,s21,s40,s49,s74,s130],[s5,s21,s40,s63,s110,s122,s133],[s5,s21,s40,s63,s113,s122,s133],[s5,s21,s45,s76,s102,s122,s127],[s6,s10,s15,s35,s55,s98,s130],[s6,s10,s45,s55,s98,s122,s127],[s8,s10,s21,s45,s74,s98,s130],[s10,s15,s26,s35,s92,s122,s135],[s10,s25,s35,s78,s98,s122,s127],[s15,s26,s41,s49,s74,s122,s127],[s21,s45,s49,s78,s110,s122,s127],[s31,s40,s54,s78,s98,s122,s127]]
def B6_11 : List (List Sig) := [[s0,s5,s10,s35,s66,s74,s130],[s2,s5,s21,s40,s113,s122,s133],[s5,s10,s21,s35,s63,s74,s131],[s5,s10,s35,s66,s89,s98,s130],[s5,s10,s45,s55,s125,s126,s127],[s5,s21,s35,s63,s102,s125,s130],[s5,s21,s35,s94,s102,s122,s133],[s5,s21,s40,s74,s114,s122,s127],[s5,s26,s70,s74,s102,s122,s127],[s10,s26,s35,s94,s98,s122,s135],[s26,s35,s68,s74,s102,s122,s127],[s26,s35,s74,s102,s119,s122,s127]]
def B6_12 : List (List Sig) := [[s4,s26,s40,s74,s98,s122,s127],[s5,s10,s21,s35,s114,s122,s133],[s5,s10,s21,s70,s74,s106,s130],[s5,s10,s35,s66,s96,s98,s130],[s5,s21,s40,s66,s74,s98,s130],[s5,s21,s40,s118,s122,s133],[s10,s26,s45,s53,s74,s98,s130],[s10,s35,s66,s78,s122,s126,s127],[s13,s31,s35,s78,s98,s122,s127],[s15,s26,s35,s76,s102,s122,s127],[s15,s26,s40,s55,s98,s122,s133],[s20,s26,s40,s49,s74,s98,s130]]
def B6_13 : List (List Sig) := [[s1,s5,s10,s21,s70,s98,s130],[s5,s15,s21,s40,s49,s74,s131],[s5,s21,s40,s77,s98,s122,s127],[s10,s26,s35,s52,s74,s98,s130],[s10,s26,s35,s94,s102,s122,s127],[s10,s26,s45,s59,s74,s98,s130],[s26,s35,s63,s85,s102,s122,s127],[s26,s35,s63,s102,s122,s125,s127],[s26,s37,s49,s74,s102,s122,s127]]
def B6_14 : List (List Sig) := [[s0,s5,s21,s40,s63,s74,s130],[s5,s10,s21,s39,s98,s122,s133],[s5,s10,s21,s70,s82,s98,s130],[s5,s10,s32,s35,s113,s122,s127],[s5,s10,s35,s66,s98,s124,s127],[s5,s11,s31,s59,s74,s122,s127],[s5,s14,s21,s35,s74,s98,s130],[s5,s21,s40,s72,s74,s98,s130],[s5,s22,s40,s49,s106,s122,s127],[s5,s23,s40,s74,s113,s122,s127],[s5,s31,s40,s49,s85,s98,s130],[s6,s21,s40,s49,s106,s122,s127],[s7,s21,s40,s74,s113,s122,s127],[s10,s26,s35,s68,s74,s122,s135],[s10,s26,s36,s49,s82,s122,s127],[s10,s35,s66,s78,s109,s122,s127],[s26,s40,s49,s78,s106,s122,s127],[s26,s40,s66,s74,s98,s122,s127],[s28,s40,s49,s74,s98,s122,s127]]
def B6_15 : List (List Sig) := [[s5,s10,s21,s35,s63,s134,s136],[s5,s10,s23,s35,s113,s122,s133],[s5,s20,s40,s55,s74,s98,s130],[s5,s21,s73,s74,s110,s122,s127],[s7,s10,s21,s35,s113,s122,s133],[s10,s15,s26,s35,s76,s122,s135],[s10,s15,s26,s35,s89,s122,s136],[s10,s26,s35,s66,s98,s122,s133],[s11,s15,s35,s55,s78,s122,s127],[s15,s21,s40,s80,s98,s122,s127],[s15,s29,s35,s74,s102,s122,s127],[s21,s40,s49,s79,s98,s122,s127],[s21,s40,s63,s78,s122,s126,s127],[s21,s40,s68,s78,s98,s122,s127]]
def B6_16 : List (List Sig) := [[s0,s26,s40,s63,s74,s122,s127],[s5,s10,s21,s61,s74,s98,s130],[s5,s10,s21,s73,s74,s98,s130],[s5,s10,s22,s35,s63,s98,s130],[s5,s10,s35,s55,s82,s106,s130],[s5,s10,s35,s66,s87,s98,s130],[s6,s10,s21,s35,s63,s98,s130],[s10,s15,s26,s36,s49,s74,s130],[s10,s19,s35,s55,s78,s98,s130],[s10,s26,s35,s63,s78,s98,s130],[s10,s26,s35,s63,s85,s122,s135],[s10,s26,s35,s63,s122,s125,s135],[s10,s26,s35,s70,s74,s98,s130],[s10,s26,s35,s96,s98,s122,s127],[s10,s26,s37,s49,s74,s122,s135],[s14,s26,s35,s74,s98,s122,s127],[s19,s26,s59,s74,s102,s122,s127],[s21,s40,s49,s78,s99,s122,s127],[s26,s40,s72,s74,s98,s122,s127]]
def B6_17 : List (List Sig) := [[s5,s10,s36,s55,s82,s122,s127],[s5,s15,s21,s40,s49,s134,s136],[s5,s20,s21,s62,s74,s98,s130],[s5,s21,s40,s63,s98,s124,s127],[s5,s21,s70,s74,s102,s122,s127],[s5,s25,s35,s74,s102,s122,s127],[s9,s21,s35,s74,s102,s122,s127],[s10,s26,s35,s63,s94,s122,s135],[s10,s34,s35,s78,s113,s122,s127],[s15,s21,s62,s78,s110,s122,s127],[s21,s40,s63,s78,s109,s122,s127],[s26,s40,s63,s74,s98,s127,s130],[s34,s35,s58,s74,s102,s122,s127]]
def B6_18 : List (List Sig) := [[s5,s10,s21,s35,s65,s122,s135],[s5,s10,s45,s55,s74,s106,s130],[s5,s11,s31,s35,s49,s74,s130],[s5,s15,s22,s40,s49,s98,s130],[s5,s18,s21,s40,s98,s122,s133],[s5,s21,s35,s54,s108,s122,s133],[s6,s15,s21,s40,s49,s98,s130],[s10,s15,s29,s35,s74,s122,s135],[s10,s15,s35,s58,s86,s98,s130],[s10,s26,s35,s55,s82,s122,s135],[s10,s26,s35,s63,s74,s102,s130],[s10,s26,s35,s63,s98,s130,s133],[s15,s26,s40,s49,s78,s98,s130],[s21,s26,s40,s63,s98,s122,s133],[s23,s35,s49,s78,s102,s122,s127],[s26,s40,s49,s82,s102,s122,s127]]
def B6_19 : List (List Sig) := [[s0,s5,s10,s31,s59,s74,s130],[s1,s5,s10,s45,s55,s98,s130],[s5,s10,s15,s36,s55,s74,s130],[s5,s10,s31,s59,s89,s98,s130],[s5,s10,s45,s58,s74,s98,s130],[s5,s10,s55,s70,s74,s98,s130],[s5,s21,s40,s85,s118,s122,s127],[s5,s21,s40,s113,s118,s122,s133],[s5,s21,s40,s118,s122,s125,s127],[s5,s21,s41,s63,s74,s122,s127],[s5,s24,s40,s74,s106,s122,s127],[s8,s21,s40,s74,s106,s122,s127],[s10,s26,s35,s63,s125,s126,s127],[s10,s26,s35,s94,s98,s122,s130],[s10,s33,s35,s78,s98,s122,s127],[s21,s48,s49,s78,s110,s122,s127],[s26,s40,s74,s106,s113,s122,s127]]
def B6_20 : List (List Sig) := [[s5,s10,s21,s36,s94,s122,s127],[s5,s10,s21,s59,s82,s123,s127],[s5,s10,s24,s35,s106,s122,s133],[s5,s10,s25,s35,s74,s122,s135],[s5,s10,s45,s55,s82,s98,s130],[s8,s10,s21,s35,s106,s122,s133],[s9,s10,s21,s35,s74,s122,s135],[s10,s15,s26,s35,s93,s122,s135],[s10,s34,s35,s58,s74,s122,s135],[s10,s35,s57,s78,s98,s122,s127],[s15,s26,s40,s49,s74,s102,s130],[s15,s26,s40,s49,s98,s130,s133],[s21,s35,s78,s108,s115,s122,s127]]
def B6_21 : List (List Sig) := [[s5,s10,s21,s35,s63,s126,s134],[s5,s10,s21,s60,s82,s122,s127],[s5,s10,s26,s35,s94,s122,s135],[s5,s12,s21,s35,s113,s122,s133],[s5,s15,s21,s40,s113,s125,s130],[s5,s15,s21,s59,s102,s124,s127],[s5,s35,s66,s85,s102,s122,s127],[s5,s40,s55,s82,s102,s122,s127],[s10,s21,s26,s35,s94,s122,s135],[s11,s21,s35,s63,s78,s122,s127],[s15,s26,s40,s49,s125,s126,s127],[s21,s35,s63,s78,s110,s122,s127],[s21,s40,s63,s78,s110,s122,s127],[s26,s40,s53,s74,s106,s122,s127],[s26,s40,s74,s98,s118,s122,s127]]
def B6_22 : List (List Sig) := [[s3,s10,s26,s35,s82,s122,s135],[s5,s10,s21,s59,s82,s122,s128],[s5,s10,s31,s36,s89,s122,s127],[s5,s10,s31,s59,s98,s124,s127],[s5,s10,s35,s66,s74,s118,s130],[s5,s15,s21,s40,s50,s122,s133],[s5,s15,s21,s41,s49,s122,s133],[s10,s31,s59,s78,s109,s122,s127],[s15,s35,s55,s86,s102,s122,s127],[s21,s35,s78,s94,s102,s122,s127],[s21,s40,s63,s78,s98,s122,s133],[s26,s35,s63,s86,s102,s122,s127]]
def B6_23 : List (List Sig) := [[s5,s10,s15,s21,s60,s74,s130],[s5,s10,s31,s35,s113,s122,s129],[s5,s10,s35,s66,s92,s98,s130],[s5,s15,s21,s40,s49,s126,s134],[s5,s15,s24,s40,s74,s98,s130],[s5,s15,s40,s55,s74,s102,s130],[s5,s21,s62,s82,s102,s122,s127],[s8,s15,s21,s40,s74,s98,s130],[s10,s26,s31,s35,s89,s122,s135],[s10,s26,s35,s69,s74,s98,s130],[s10,s34,s35,s91,s98,s122,s127]]
def B6_24 : List (List Sig) := [[s4,s5,s21,s40,s98,s122,s133],[s5,s10,s21,s45,s89,s126,s130],[s5,s10,s31,s59,s87,s98,s130],[s5,s10,s35,s66,s78,s98,s130],[s5,s10,s35,s66,s85,s122,s135],[s5,s16,s21,s40,s49,s122,s133],[s5,s21,s40,s52,s74,s98,s130],[s5,s21,s40,s74,s118,s122,s133],[s5,s21,s40,s82,s113,s122,s133],[s5,s21,s40,s94,s102,s122,s127],[s5,s21,s42,s49,s74,s98,s130],[s10,s31,s35,s49,s78,s126,s130],[s19,s21,s40,s49,s78,s98,s130]]
def B6_25 : List (List Sig) := [[s5,s10,s21,s36,s63,s74,s130],[s5,s10,s21,s59,s106,s122,s129],[s5,s10,s21,s70,s74,s123,s127],[s5,s10,s21,s70,s74,s130,s135],[s5,s15,s21,s40,s113,s122,s134],[s5,s15,s21,s62,s74,s102,s130],[s5,s20,s21,s59,s74,s102,s130],[s5,s21,s40,s63,s74,s118,s130],[s5,s21,s45,s49,s102,s124,s127],[s10,s21,s39,s78,s98,s122,s127],[s10,s26,s35,s63,s86,s122,s135],[s10,s26,s35,s95,s98,s122,s127],[s15,s26,s40,s53,s74,s98,s130],[s18,s26,s35,s74,s102,s122,s127]]
def B6_26 : List (List Sig) := [[s5,s10,s17,s21,s59,s98,s130],[s5,s10,s31,s35,s51,s98,s130],[s5,s10,s31,s62,s74,s98,s130],[s5,s10,s35,s66,s74,s102,s130],[s5,s10,s35,s66,s98,s130,s133],[s5,s21,s40,s66,s98,s122,s133],[s5,s21,s40,s89,s108,s122,s127],[s5,s31,s40,s89,s102,s122,s127],[s6,s10,s35,s66,s98,s122,s127],[s10,s15,s26,s35,s89,s126,s130],[s10,s26,s35,s49,s82,s123,s127],[s15,s26,s40,s58,s74,s98,s130],[s15,s26,s40,s59,s74,s98,s130],[s26,s31,s40,s49,s74,s98,s130],[s26,s40,s52,s74,s98,s122,s127],[s26,s42,s49,s74,s98,s122,s127]]
def B6_27 : List (List Sig) := [[s1,s10,s26,s35,s63,s98,s130],[s5,s10,s21,s35,s94,s122,s135],[s5,s10,s21,s70,s74,s122,s128],[s5,s10,s21,s71,s74,s122,s127],[s5,s10,s35,s66,s125,s126,s127],[s5,s21,s40,s63,s78,s98,s130],[s5,s21,s40,s70,s74,s98,s130],[s5,s21,s48,s49,s74,s102,s130],[s10,s19,s35,s58,s74,s98,s130],[s10,s26,s35,s45,s89,s122,s135],[s10,s26,s36,s63,s74,s122,s127],[s12,s26,s35,s89,s98,s122,s127],[s15,s26,s35,s49,s102,s124,s127]]
def B6_28 : List (List Sig) := [[s0,s5,s21,s40,s63,s122,s133],[s5,s10,s21,s70,s74,s120,s130],[s5,s10,s31,s35,s50,s74,s130],[s5,s14,s21,s35,s98,s122,s133],[s5,s21,s40,s72,s98,s122,s133],[s10,s18,s26,s35,s74,s122,s135],[s10,s26,s35,s49,s82,s122,s128],[s10,s26,s35,s63,s82,s98,s130],[s10,s26,s45,s89,s109,s122,s127],[s10,s35,s69,s86,s98,s122,s127],[s21,s35,s63,s86,s102,s122,s127]]
def B6_29 : List (List Sig) := [[s1,s15,s26,s40,s49,s98,s130],[s5,s10,s35,s55,s82,s123,s127],[s5,s10,s35,s69,s74,s98,s130],[s5,s21,s40,s63,s74,s102,s130],[s5,s21,s40,s63,s98,s130,s133],[s5,s22,s40,s63,s98,s122,s127],[s5,s31,s40,s55,s74,s98,s130],[s5,s31,s59,s85,s102,s122,s127],[s6,s21,s40,s63,s98,s122,s127],[s18,s21,s40,s78,s98,s122,s127],[s26,s40,s63,s78,s98,s122,s127],[s26,s40,s70,s74,s98,s122,s127],[s31,s35,s54,s78,s102,s122,s127]]
def B6_30 : List (List Sig) := [[s5,s10,s21,s45,s89,s113,s130],[s5,s21,s40,s63,s125,s126,s127],[s10,s15,s26,s35,s49,s124,s135],[s10,s15,s26,s35,s51,s122,s135],[s10,s26,s35,s82,s100,s122,s127],[s26,s40,s45,s49,s74,s98,s130],[s26,s40,s82,s89,s98,s122,s127]]
def B6_31 : List (List Sig) := [[s4,s26,s35,s74,s102,s122,s127],[s5,s10,s21,s35,s118,s124,s127],[s5,s10,s34,s59,s74,s98,s130],[s5,s10,s35,s55,s82,s122,s128],[s5,s10,s45,s55,s74,s123,s127],[s5,s10,s45,s55,s74,s130,s135],[s5,s21,s40,s106,s113,s122,s133],[s5,s26,s40,s74,s118,s122,s127],[s10,s15,s27,s35,s49,s98,s130],[s10,s26,s35,s74,s101,s122,s127],[s10,s26,s35,s82,s94,s122,s135],[s15,s40,s58,s86,s98,s122,s127],[s19,s21,s40,s53,s74,s98,s130],[s20,s26,s35,s49,s74,s102,s130],[s21,s35,s49,s78,s103,s122,s127],[s26,s40,s63,s74,s102,s122,s127],[s26,s40,s63,s98,s122,s127,s133],[s31,s40,s49,s86,s98,s122,s127]]
def B6_32 : List (List Sig) := [[s5,s10,s21,s35,s94,s123,s127],[s5,s10,s21,s70,s98,s122,s129],[s5,s10,s31,s59,s78,s98,s130],[s5,s10,s59,s66,s74,s98,s130],[s5,s21,s35,s77,s102,s122,s127],[s5,s21,s39,s74,s102,s122,s127],[s5,s21,s44,s74,s98,s122,s127],[s5,s48,s55,s74,s102,s122,s127],[s10,s17,s26,s35,s49,s98,s130],[s10,s35,s66,s78,s98,s122,s127],[s10,s40,s66,s78,s98,s122,s127]]
def B6_33 : List (List Sig) := [[s5,s10,s21,s37,s113,s122,s133],[s5,s10,s21,s38,s82,s122,s135],[s5,s10,s21,s45,s113,s124,s127],[s5,s10,s31,s35,s49,s74,s131],[s5,s10,s31,s38,s74,s98,s130],[s5,s10,s45,s55,s74,s122,s128],[s5,s15,s22,s59,s102,s122,s127],[s5,s21,s35,s72,s74,s102,s130],[s5,s21,s40,s53,s106,s122,s133],[s5,s21,s40,s98,s118,s122,s133],[s6,s15,s21,s59,s102,s122,s127],[s15,s21,s41,s49,s78,s122,s127],[s15,s26,s59,s78,s102,s122,s127],[s26,s35,s66,s74,s102,s122,s127],[s28,s35,s49,s74,s102,s122,s127]]
def B6_34 : List (List Sig) := [[s4,s10,s26,s35,s74,s122,s135],[s5,s10,s21,s35,s94,s122,s128],[s5,s10,s21,s59,s111,s122,s133],[s5,s10,s31,s35,s89,s123,s127],[s5,s10,s31,s59,s74,s102,s130],[s5,s10,s31,s59,s98,s130,s133],[s5,s10,s35,s55,s106,s122,s129],[s5,s10,s35,s66,s74,s106,s130],[s5,s20,s35,s55,s74,s102,s130],[s5,s21,s40,s59,s106,s122,s133],[s5,s21,s70,s78,s102,s122,s127],[s6,s10,s31,s59,s98,s122,s127],[s10,s26,s35,s94,s122,s127,s135],[s10,s34,s35,s49,s86,s98,s130],[s15,s21,s35,s80,s102,s122,s127],[s15,s26,s38,s74,s102,s122,s127],[s21,s35,s49,s79,s102,s122,s127],[s21,s35,s68,s78,s102,s122,s127],[s21,s35,s78,s102,s119,s122,s127],[s21,s40,s78,s95,s98,s122,s127]]
def B6_35 : List (List Sig) := [[s1,s5,s10,s35,s66,s98,s130],[s4,s21,s40,s78,s98,s122,s127],[s5,s10,s17,s35,s55,s98,s130],[s5,s10,s21,s35,s77,s122,s135],[s5,s10,s21,s39,s74,s122,s135],[s5,s10,s31,s59,s74,s116,s130],[s5,s10,s31,s59,s125,s126,s127],[s5,s10,s36,s66,s74,s122,s127],[s10,s21,s45,s53,s78,s98,s130],[s10,s31,s35,s80,s98,s122,s127],[s26,s35,s72,s74,s102,s122,s127],[s26,s40,s54,s82,s98,s122,s127]]
def B6_36 : List (List Sig) := [[s0,s10,s35,s66,s78,s122,s127],[s5,s10,s21,s47,s74,s98,s130],[s5,s10,s31,s35,s89,s122,s128],[s5,s10,s35,s66,s82,s98,s130],[s5,s21,s35,s63,s102,s124,s127],[s10,s26,s35,s66,s74,s122,s135],[s10,s28,s35,s49,s74,s122,s135],[s21,s37,s49,s78,s102,s122,s127],[s26,s40,s69,s74,s98,s122,s127]]
def B6_37 : List (List Sig) := [[s5,s10,s31,s35,s49,s134,s136],[s5,s13,s21,s45,s74,s98,s130],[s5,s15,s24,s40,s98,s122,s133],[s5,s21,s40,s63,s74,s106,s130],[s5,s21,s40,s74,s118,s122,s127],[s5,s22,s45,s49,s102,s122,s127],[s6,s21,s45,s49,s102,s122,s127],[s8,s15,s21,s40,s98,s122,s133],[s10,s15,s26,s38,s74,s122,s135],[s10,s21,s35,s68,s78,s122,s135],[s13,s26,s35,s82,s98,s122,s127],[s15,s26,s40,s54,s74,s98,s130],[s15,s26,s40,s62,s74,s98,s130],[s21,s40,s66,s78,s98,s122,s127],[s26,s40,s63,s74,s98,s122,s130],[s26,s45,s49,s78,s102,s122,s127]]
def B6_38 : List (List Sig) := [[s1,s5,s21,s40,s63,s98,s130],[s5,s10,s21,s35,s118,s122,s133],[s5,s10,s21,s40,s118,s122,s133],[s5,s10,s45,s55,s98,s122,s129],[s5,s10,s45,s66,s74,s98,s130],[s5,s21,s40,s52,s98,s122,s133],[s5,s21,s40,s74,s121,s122,s127],[s5,s21,s42,s49,s98,s122,s133],[s6,s10,s31,s35,s49,s98,s130],[s10,s26,s35,s49,s82,s122,s136],[s10,s26,s35,s63,s89,s122,s135],[s10,s26,s35,s72,s74,s122,s135],[s10,s26,s35,s89,s99,s122,s127]]
def B6_39 : List (List Sig) := [[s0,s21,s40,s63,s78,s122,s127],[s2,s10,s26,s35,s89,s122,s135],[s5,s10,s21,s35,s63,s124,s135],[s5,s10,s21,s36,s63,s122,s133],[s5,s10,s21,s70,s122,s133,s135],[s5,s21,s40,s63,s118,s122,s133],[s5,s40,s66,s74,s102,s122,s127],[s10,s26,s34,s35,s89,s122,s135],[s10,s26,s35,s63,s74,s123,s127],[s10,s26,s35,s63,s74,s130,s135],[s10,s26,s37,s89,s98,s122,s127],[s13,s15,s26,s35,s74,s98,s130],[s14,s21,s35,s78,s98,s122,s127],[s19,s21,s59,s78,s102,s122,s127],[s21,s40,s72,s78,s98,s122,s127],[s26,s40,s48,s49,s74,s98,s130],[s26,s40,s49,s75,s98,s122,s127]]
def B6_40 : List (List Sig) := [[s1,s26,s40,s63,s98,s122,s127],[s5,s10,s23,s59,s74,s98,s130],[s5,s21,s40,s89,s106,s122,s133],[s7,s10,s21,s59,s74,s98,s130],[s10,s34,s35,s93,s98,s122,s127],[s10,s35,s58,s78,s106,s122,s127],[s20,s40,s55,s78,s98,s122,s127],[s26,s31,s40,s49,s98,s122,s133],[s26,s35,s74,s102,s118,s122,s127]]
def B6_41 : List (List Sig) := [[s5,s10,s31,s35,s92,s122,s135],[s5,s10,s31,s35,s113,s125,s130],[s5,s21,s40,s70,s98,s122,s133],[s10,s26,s35,s63,s74,s122,s128],[s15,s26,s40,s49,s74,s123,s127],[s15,s26,s40,s49,s74,s130,s135],[s19,s26,s40,s74,s113,s122,s127],[s21,s35,s63,s78,s102,s122,s133],[s26,s35,s40,s63,s74,s98,s130],[s26,s40,s49,s63,s74,s98,s130]]
def B6_42 : List (List Sig) := [[s2,s26,s40,s49,s74,s98,s130],[s5,s10,s21,s70,s74,s130,s136],[s5,s10,s31,s59,s74,s106,s130],[s5,s21,s40,s49,s106,s122,s129],[s5,s21,s40,s74,s101,s122,s127],[s5,s21,s40,s82,s115,s122,s127],[s5,s21,s70,s74,s102,s122,s130],[s5,s24,s45,s74,s102,s122,s127],[s8,s21,s45,s74,s102,s122,s127],[s10,s27,s35,s63,s98,s122,s127],[s21,s40,s78,s106,s113,s122,s127],[s26,s34,s40,s49,s74,s98,s130]]
def B6_43 : List (List Sig) := [[s1,s5,s10,s31,s59,s98,s130],[s5,s10,s21,s35,s101,s122,s133],[s5,s10,s21,s59,s82,s126,s130],[s5,s10,s21,s59,s106,s125,s130],[s5,s10,s22,s35,s118,s122,s127],[s5,s10,s24,s35,s82,s122,s135],[s5,s11,s21,s45,s89,s122,s127],[s5,s21,s40,s63,s102,s122,s133],[s5,s31,s40,s55,s98,s122,s133],[s6,s10,s21,s35,s118,s122,s127],[s8,s10,s21,s35,s82,s122,s135],[s8,s10,s31,s35,s74,s98,s130],[s10,s26,s35,s49,s84,s122,s135],[s10,s26,s35,s74,s118,s122,s135],[s10,s26,s35,s78,s118,s122,s127],[s10,s26,s35,s82,s113,s122,s135],[s10,s26,s35,s83,s98,s122,s127],[s11,s31,s35,s49,s78,s122,s127],[s15,s26,s40,s49,s74,s122,s128],[s15,s26,s40,s63,s74,s98,s130]]
def B6_44 : List (List Sig) := [[s5,s10,s21,s35,s94,s122,s136],[s5,s10,s31,s59,s82,s98,s130],[s5,s21,s48,s54,s74,s98,s130],[s5,s21,s48,s62,s74,s98,s130],[s10,s15,s35,s58,s78,s98,s130],[s10,s15,s36,s55,s78,s122,s127],[s10,s45,s58,s78,s98,s122,s127],[s15,s27,s40,s49,s98,s122,s127],[s21,s40,s53,s78,s106,s122,s127],[s21,s40,s78,s98,s118,s122,s127],[s26,s45,s53,s74,s102,s122,s127]]
def B6_45 : List (List Sig) := [[s1,s5,s21,s70,s102,s122,s127],[s5,s10,s22,s45,s113,s122,s127],[s5,s10,s45,s55,s122,s133,s135],[s5,s21,s40,s54,s106,s122,s133],[s5,s21,s40,s62,s106,s122,s133],[s5,s21,s43,s74,s106,s122,s127],[s6,s10,s21,s45,s113,s122,s127],[s10,s26,s35,s53,s82,s122,s135],[s10,s26,s45,s78,s113,s122,s127],[s11,s15,s26,s35,s89,s122,s127],[s15,s26,s40,s74,s100,s122,s127],[s19,s21,s40,s53,s98,s122,s133],[s26,s35,s52,s74,s102,s122,s127],[s26,s45,s59,s74,s102,s122,s127]]
def B6_46 : List (List Sig) := [[s5,s12,s21,s59,s74,s98,s130],[s5,s15,s21,s40,s113,s124,s127],[s10,s26,s35,s58,s82,s122,s135],[s10,s26,s35,s59,s82,s122,s135],[s10,s26,s35,s63,s98,s122,s129],[s26,s48,s62,s74,s98,s122,s127]]
def B6_47 : List (List Sig) := [[s5,s10,s21,s46,s89,s122,s127],[s5,s10,s31,s36,s49,s74,s130],[s5,s10,s35,s66,s74,s123,s127],[s5,s10,s35,s66,s74,s130,s135],[s5,s13,s21,s35,s106,s122,s133],[s5,s21,s35,s72,s102,s122,s133],[s10,s26,s35,s91,s106,s122,s127],[s10,s26,s59,s82,s109,s122,s127],[s10,s35,s58,s84,s98,s122,s127],[s34,s40,s49,s86,s98,s122,s127]]
def B6_48 : List (List Sig) := [[s5,s10,s21,s70,s74,s126,s130],[s5,s10,s45,s55,s74,s130,s136],[s5,s21,s61,s74,s102,s122,s127],[s5,s21,s73,s74,s102,s122,s127],[s5,s22,s35,s63,s102,s122,s127],[s6,s21,s35,s63,s102,s122,s127],[s10,s26,s35,s49,s88,s122,s135],[s10,s26,s35,s52,s74,s122,s135],[s10,s26,s35,s84,s113,s122,s127],[s10,s26,s45,s59,s74,s122,s135],[s15,s21,s40,s53,s78,s98,s130],[s15,s24,s40,s78,s98,s122,s127],[s15,s26,s40,s49,s98,s122,s129],[s15,s40,s55,s78,s102,s122,s127],[s18,s21,s35,s78,s102,s122,s127],[s20,s26,s35,s54,s74,s98,s130],[s26,s35,s63,s74,s102,s122,s135],[s26,s35,s63,s78,s102,s122,s127],[s26,s35,s70,s74,s102,s122,s127]]
def B6_49 : List (List Sig) := [[s5,s10,s21,s35,s96,s122,s135],[s5,s10,s31,s70,s74,s98,s130],[s5,s10,s35,s66,s74,s122,s128],[s5,s14,s21,s35,s74,s122,s135],[s5,s15,s21,s43,s74,s98,s130],[s7,s10,s35,s55,s74,s98,s130],[s10,s15,s26,s59,s74,s109,s130],[s10,s26,s35,s49,s82,s126,s130],[s21,s40,s52,s78,s98,s122,s127],[s21,s42,s49,s78,s98,s122,s127],[s26,s35,s82,s89,s102,s122,s127]]
def B6_50 : List (List Sig) := [[s5,s10,s15,s21,s59,s98,s132],[s5,s10,s21,s70,s74,s109,s130],[s5,s10,s21,s70,s85,s98,s130],[s5,s10,s21,s70,s98,s125,s130],[s5,s21,s40,s63,s74,s123,s127],[s5,s21,s40,s63,s74,s130,s135],[s10,s21,s36,s63,s78,s122,s127],[s10,s26,s35,s90,s98,s122,s127],[s15,s35,s58,s86,s102,s122,s127],[s31,s35,s49,s86,s102,s122,s127]]
def B6_51 : List (List Sig) := [[s5,s10,s21,s35,s63,s123,s133],[s5,s10,s21,s70,s94,s98,s130],[s5,s10,s22,s35,s63,s122,s135],[s5,s21,s40,s49,s111,s122,s133],[s5,s21,s40,s63,s106,s122,s133],[s5,s31,s40,s49,s74,s102,s130],[s6,s10,s21,s35,s63,s122,s135],[s10,s26,s35,s63,s74,s122,s136],[s10,s26,s35,s63,s78,s122,s135],[s10,s26,s35,s70,s74,s122,s135],[s10,s26,s45,s91,s98,s122,s127],[s10,s35,s66,s78,s102,s122,s127],[s15,s26,s43,s74,s98,s122,s127]]
def B6_52 : List (List Sig) := [[s5,s10,s35,s55,s82,s126,s130],[s5,s10,s35,s55,s106,s125,s130],[s5,s21,s40,s63,s74,s122,s128],[s5,s21,s59,s75,s102,s122,s127],[s10,s26,s35,s82,s89,s122,s135],[s10,s26,s70,s74,s109,s122,s127],[s10,s35,s58,s88,s98,s122,s127],[s12,s26,s35,s49,s74,s98,s130],[s21,s40,s70,s78,s98,s122,s127],[s26,s40,s63,s74,s122,s127,s135]]
def B6_53 : List (List Sig) := [[s5,s10,s32,s59,s98,s122,s127],[s5,s15,s21,s40,s49,s123,s133],[s5,s19,s21,s40,s113,s122,s133],[s5,s21,s48,s74,s115,s122,s127],[s5,s21,s48,s74,s117,s122,s127],[s10,s15,s35,s58,s86,s122,s135],[s10,s26,s35,s63,s122,s133,s135],[s10,s26,s45,s49,s74,s109,s130],[s21,s35,s78,s95,s102,s122,s127]]
def B6_54 : List (List Sig) := [[s4,s21,s35,s78,s102,s122,s127],[s5,s10,s21,s45,s49,s98,s132],[s5,s10,s21,s70,s74,s111,s130],[s5,s10,s21,s70,s74,s113,s130],[s5,s10,s23,s35,s89,s122,s135],[s5,s10,s35,s66,s98,s122,s129],[s5,s10,s45,s55,s74,s126,s130],[s5,s21,s40,s78,s118,s122,s127],[s5,s21,s45,s54,s74,s102,s130],[s5,s31,s40,s85,s113,s122,s127],[s7,s10,s21,s35,s89,s122,s135],[s10,s21,s35,s78,s101,s122,s127],[s10,s35,s69,s78,s98,s122,s127],[s21,s40,s63,s78,s102,s122,s127],[s26,s35,s54,s82,s102,s122,s127],[s31,s40,s55,s78,s98,s122,s127]]
def B6_55 : List (List Sig) := [[s5,s10,s21,s35,s94,s126,s130],[s5,s10,s31,s59,s74,s123,s127],[s5,s10,s31,s59,s74,s130,s135],[s5,s12,s35,s55,s74,s98,s130],[s15,s26,s40,s49,s122,s133,s135],[s26,s35,s69,s74,s102,s122,s127]]
def B6_56 : List (List Sig) := [[s5,s10,s31,s60,s74,s122,s127],[s5,s10,s45,s55,s74,s109,s130],[s5,s10,s45,s55,s85,s98,s130],[s5,s10,s45,s55,s98,s125,s130],[s5,s21,s40,s118,s122,s127,s133],[s5,s40,s55,s74,s108,s122,s127],[s10,s15,s26,s35,s49,s98,s132],[s10,s15,s35,s55,s78,s123,s127],[s10,s26,s35,s63,s74,s130,s136],[s10,s34,s59,s78,s98,s122,s127],[s15,s26,s35,s54,s74,s102,s130],[s21,s35,s66,s78,s102,s122,s127],[s26,s35,s63,s74,s102,s122,s130],[s26,s40,s63,s74,s98,s130]]
def B6_57 : List (List Sig) := [[s5,s10,s31,s35,s89,s126,s130],[s5,s10,s31,s59,s74,s122,s128],[s5,s10,s32,s35,s49,s98,s130],[s5,s10,s35,s56,s106,s122,s127],[s5,s15,s21,s40,s100,s122,s133],[s5,s21,s40,s63,s98,s122,s129],[s5,s23,s40,s49,s74,s98,s130],[s7,s21,s40,s49,s74,s98,s130],[s10,s26,s35,s54,s82,s122,s135],[s10,s26,s35,s94,s122,s126,s127],[s10,s35,s66,s78,s98,s122,s130],[s15,s21,s38,s78,s102,s122,s127]]
def B6_58 : List (List Sig) := [[s5,s10,s21,s35,s95,s122,s135],[s5,s15,s21,s40,s115,s122,s133],[s5,s15,s21,s40,s117,s122,s133],[s5,s15,s22,s40,s113,s122,s127],[s5,s21,s40,s73,s74,s98,s130],[s5,s21,s48,s62,s98,s122,s133],[s5,s21,s62,s74,s108,s122,s127],[s5,s31,s62,s74,s102,s122,s127],[s6,s15,s21,s40,s113,s122,s127],[s10,s26,s35,s49,s94,s122,s135],[s10,s26,s35,s69,s74,s122,s135],[s10,s31,s38,s78,s98,s122,s127],[s15,s26,s40,s49,s74,s130,s136],[s15,s26,s40,s78,s113,s122,s127],[s21,s35,s72,s78,s102,s122,s127],[s26,s35,s49,s75,s102,s122,s127]]
def B6_59 : List (List Sig) := [[s1,s26,s35,s63,s102,s122,s127],[s5,s10,s15,s35,s55,s98,s132],[s5,s10,s21,s70,s98,s130,s134],[s5,s21,s45,s74,s104,s122,s127],[s10,s26,s35,s89,s106,s122,s135],[s10,s26,s35,s94,s109,s122,s127],[s10,s28,s35,s89,s98,s122,s127],[s20,s35,s55,s78,s102,s122,s127]]
def B6_60 : List (List Sig) := [[s5,s10,s45,s55,s74,s111,s130],[s5,s10,s45,s55,s74,s113,s130],[s5,s12,s21,s35,s89,s122,s135],[s5,s21,s40,s49,s106,s125,s130],[s5,s21,s40,s106,s118,s122,s133],[s10,s15,s26,s35,s94,s122,s135],[s10,s34,s35,s49,s78,s98,s130],[s21,s40,s63,s78,s98,s122,s130],[s26,s40,s73,s74,s98,s122,s127]]
def B6_61 : List (List Sig) := [[s5,s10,s15,s35,s56,s98,s130],[s5,s10,s35,s66,s122,s133,s135],[s5,s10,s45,s56,s98,s122,s127],[s10,s26,s35,s49,s75,s122,s135],[s15,s26,s35,s74,s104,s122,s127],[s15,s26,s40,s59,s74,s122,s135]]
def B6_62 : List (List Sig) := [[s1,s10,s26,s35,s63,s122,s135],[s5,s10,s26,s70,s74,s98,s130],[s5,s10,s31,s59,s98,s122,s129],[s5,s11,s21,s59,s82,s122,s127],[s5,s21,s40,s70,s74,s122,s135],[s5,s21,s40,s74,s118,s122,s130],[s10,s21,s35,s63,s78,s123,s127],[s10,s26,s35,s63,s74,s126,s130],[s10,s26,s35,s68,s74,s98,s130]]
def B6_63 : List (List Sig) := [[s5,s10,s31,s35,s89,s113,s130],[s5,s15,s21,s43,s98,s122,s133],[s10,s26,s35,s63,s82,s122,s135],[s15,s27,s35,s49,s102,s122,s127],[s21,s35,s78,s102,s118,s122,s127],[s21,s40,s84,s91,s98,s122,s127],[s26,s40,s74,s94,s98,s122,s127]]
def B6_64 : List (List Sig) := [[s5,s10,s21,s70,s109,s122,s133],[s5,s10,s35,s66,s74,s130,s136],[s5,s11,s15,s21,s59,s74,s130],[s5,s20,s21,s40,s113,s122,s133],[s5,s21,s40,s49,s106,s122,s134],[s5,s21,s40,s63,s122,s133,s135],[s5,s21,s42,s74,s113,s122,s127],[s10,s26,s35,s63,s74,s109,s130],[s10,s26,s35,s63,s85,s98,s130],[s10,s26,s35,s63,s98,s125,s130],[s10,s26,s37,s49,s74,s98,s130],[s10,s29,s35,s82,s98,s122,s127],[s15,s21,s40,s49,s78,s123,s127],[s15,s26,s40,s49,s74,s126,s130],[s19,s21,s40,s78,s113,s122,s127]]
def B6_65 : List (List Sig) := [[s1,s5,s21,s40,s118,s122,s127],[s5,s10,s21,s35,s63,s98,s132],[s5,s10,s21,s35,s64,s74,s130],[s5,s10,s45,s55,s98,s130,s134],[s5,s21,s40,s49,s108,s122,s133],[s5,s21,s40,s74,s120,s122,s127],[s5,s40,s55,s85,s106,s122,s127],[s10,s26,s35,s63,s94,s98,s130],[s26,s40,s45,s49,s74,s122,s135]]
def B6_66 : List (List Sig) := [[s5,s10,s21,s35,s65,s98,s130],[s5,s10,s21,s35,s120,s122,s133],[s5,s10,s31,s35,s113,s124,s127],[s5,s10,s66,s70,s74,s98,s130],[s5,s21,s35,s74,s105,s122,s127],[s10,s15,s27,s35,s49,s122,s135],[s10,s15,s29,s35,s74,s98,s130],[s10,s21,s35,s78,s118,s122,s135],[s15,s26,s40,s49,s74,s109,s130],[s15,s26,s40,s49,s85,s98,s130],[s15,s26,s40,s49,s98,s125,s130],[s15,s26,s59,s74,s110,s122,s127],[s34,s35,s49,s86,s102,s122,s127]]
def B6_67 : List (List Sig) := [[s5,s10,s37,s55,s74,s98,s130],[s5,s11,s21,s70,s74,s122,s127],[s5,s15,s21,s40,s49,s98,s132],[s5,s21,s40,s63,s74,s130,s136],[s5,s21,s70,s74,s110,s122,s127],[s10,s17,s26,s35,s49,s122,s135],[s10,s19,s26,s59,s74,s98,s130],[s10,s34,s35,s53,s74,s98,s130],[s15,s24,s35,s78,s102,s122,s127],[s21,s45,s53,s78,s102,s122,s127]]
def B6_68 : List (List Sig) := [[s5,s10,s21,s59,s106,s124,s127],[s5,s10,s21,s70,s74,s98,s130],[s5,s10,s25,s35,s74,s98,s130],[s5,s11,s21,s45,s49,s74,s130],[s5,s21,s47,s74,s102,s122,s127],[s5,s31,s40,s54,s74,s98,s130],[s9,s10,s21,s35,s74,s98,s130],[s10,s26,s35,s65,s98,s122,s127],[s10,s31,s35,s53,s78,s98,s130],[s10,s34,s35,s58,s74,s98,s130],[s11,s26,s35,s49,s82,s122,s127],[s15,s21,s40,s78,s100,s122,s127],[s21,s35,s52,s78,s102,s122,s127],[s21,s45,s59,s78,s102,s122,s127]]
def B6_69 : List (List Sig) := [[s5,s10,s31,s59,s122,s133,s135],[s5,s15,s40,s55,s85,s98,s130],[s5,s20,s21,s35,s115,s122,s133],[s10,s34,s35,s49,s86,s122,s135],[s21,s48,s62,s78,s98,s122,s127]]
def B6_70 : List (List Sig) := [[s5,s10,s35,s66,s74,s126,s130],[s5,s13,s21,s35,s82,s122,s135],[s5,s13,s31,s35,s74,s98,s130],[s5,s21,s40,s76,s106,s122,s127],[s5,s21,s62,s74,s112,s122,s127],[s11,s15,s26,s35,s49,s74,s130],[s15,s26,s40,s49,s74,s110,s130],[s20,s26,s40,s89,s98,s122,s127],[s26,s45,s49,s74,s110,s122,s127]]
def B6_71 : List (List Sig) := [[s5,s10,s21,s35,s118,s122,s129],[s5,s11,s35,s55,s82,s122,s127],[s5,s21,s40,s74,s107,s122,s127],[s5,s23,s40,s49,s98,s122,s133],[s7,s21,s40,s49,s98,s122,s133],[s21,s35,s63,s78,s102,s122,s135],[s21,s35,s70,s78,s102,s122,s127]]
def B6_72 : List (List Sig) := [[s0,s5,s10,s21,s70,s74,s130],[s5,s10,s21,s35,s107,s122,s133],[s5,s10,s21,s37,s89,s122,s135],[s5,s10,s21,s46,s49,s74,s130],[s5,s10,s21,s70,s89,s98,s130],[s5,s10,s31,s59,s74,s130,s136],[s5,s10,s35,s66,s74,s109,s130],[s5,s10,s35,s66,s85,s98,s130],[s5,s10,s35,s66,s98,s125,s130],[s5,s21,s40,s73,s98,s122,s133],[s5,s23,s59,s74,s102,s122,s127],[s7,s21,s59,s74,s102,s122,s127],[s10,s31,s36,s49,s78,s122,s127]]
def B6_73 : List (List Sig) := [[s5,s10,s21,s45,s113,s122,s129],[s5,s10,s35,s66,s94,s98,s130],[s5,s11,s15,s35,s55,s74,s130],[s5,s11,s45,s55,s74,s122,s127],[s5,s21,s40,s63,s74,s126,s130],[s5,s21,s40,s68,s74,s98,s130],[s10,s21,s35,s53,s84,s122,s135],[s10,s26,s35,s63,s86,s98,s130],[s10,s26,s35,s63,s98,s130,s134],[s10,s26,s35,s94,s122,s135],[s31,s35,s55,s78,s102,s122,s127]]
def B6_74 : List (List Sig) := [[s5,s10,s21,s45,s116,s122,s133],[s5,s11,s21,s35,s94,s122,s127],[s10,s15,s26,s36,s89,s122,s127],[s10,s26,s35,s97,s98,s122,s127],[s13,s15,s26,s35,s74,s122,s135],[s15,s21,s43,s78,s98,s122,s127]]
def B6_75 : List (List Sig) := [[s5,s10,s21,s70,s98,s124,s127],[s5,s15,s21,s62,s74,s110,s130],[s5,s21,s40,s63,s74,s109,s130],[s5,s21,s40,s63,s85,s98,s130],[s5,s21,s40,s63,s98,s125,s130],[s5,s21,s40,s94,s98,s122,s133],[s10,s21,s70,s78,s109,s122,s127],[s15,s26,s40,s49,s86,s98,s130],[s15,s26,s40,s49,s98,s130,s134],[s26,s40,s63,s74,s122,s126,s127],[s26,s40,s68,s74,s98,s122,s127]]
def B6_76 : List (List Sig) := [[s5,s10,s16,s21,s59,s74,s130],[s5,s10,s21,s35,s83,s122,s135],[s5,s10,s21,s45,s51,s98,s130],[s5,s10,s35,s66,s74,s113,s130],[s5,s11,s31,s35,s89,s122,s127],[s10,s18,s26,s35,s74,s98,s130],[s15,s26,s40,s76,s98,s122,s127],[s26,s35,s40,s63,s74,s122,s135],[s26,s40,s49,s74,s99,s122,s127],[s31,s40,s49,s78,s102,s122,s127]]
def B6_77 : List (List Sig) := [[s5,s10,s33,s35,s74,s98,s130],[s5,s10,s35,s55,s106,s124,s127],[s5,s10,s46,s55,s74,s122,s127],[s5,s21,s40,s49,s112,s122,s133],[s5,s21,s40,s75,s113,s122,s127],[s5,s21,s48,s49,s74,s110,s130],[s5,s31,s40,s74,s115,s122,s127],[s10,s26,s35,s94,s98,s122,s127],[s10,s26,s40,s94,s98,s122,s127],[s15,s26,s62,s74,s110,s122,s127],[s26,s40,s63,s74,s109,s122,s127],[s26,s40,s63,s85,s98,s122,s127],[s26,s40,s63,s98,s122,s125,s127]]
def B6_78 : List (List Sig) := [[s0,s5,s10,s45,s55,s74,s130],[s5,s10,s21,s45,s50,s74,s130],[s5,s10,s31,s59,s74,s126,s130],[s5,s10,s35,s57,s74,s98,s130],[s5,s10,s45,s55,s89,s98,s130],[s5,s21,s31,s40,s113,s122,s133],[s5,s21,s40,s64,s74,s122,s127],[s6,s10,s31,s35,s113,s122,s127],[s10,s15,s26,s35,s51,s98,s130],[s15,s26,s40,s89,s102,s122,s127]]
def B6_79 : List (List Sig) := [[s5,s10,s15,s21,s59,s74,s131],[s5,s10,s21,s35,s64,s122,s133],[s5,s11,s21,s35,s63,s74,s130],[s5,s15,s21,s59,s102,s125,s130],[s5,s21,s40,s63,s74,s110,s130],[s5,s21,s40,s63,s74,s113,s130],[s5,s21,s40,s63,s98,s122,s134],[s10,s15,s35,s55,s78,s126,s130],[s15,s29,s40,s74,s98,s122,s127],[s21,s35,s63,s78,s102,s122,s130],[s26,s48,s49,s74,s110,s122,s127]]
def B6_80 : List (List Sig) := [[s5,s10,s22,s59,s106,s122,s127],[s5,s10,s31,s59,s74,s109,s130],[s5,s10,s31,s59,s85,s98,s130],[s5,s10,s31,s59,s98,s125,s130],[s5,s21,s35,s40,s118,s122,s133],[s5,s21,s40,s49,s118,s122,s133],[s6,s10,s21,s59,s106,s122,s127],[s10,s15,s26,s35,s49,s125,s136],[s10,s26,s59,s78,s106,s122,s127],[s12,s35,s55,s78,s98,s122,s127],[s26,s35,s74,s108,s115,s122,s127]]
def B6_81 : List (List Sig) := [[s0,s10,s26,s35,s94,s122,s127],[s5,s10,s35,s66,s98,s130,s134],[s5,s10,s45,s55,s98,s124,s127],[s5,s25,s40,s74,s98,s122,s127],[s9,s21,s40,s74,s98,s122,s127],[s10,s19,s26,s35,s89,s122,s135],[s10,s45,s55,s78,s109,s122,s127],[s11,s26,s35,s63,s74,s122,s127],[s15,s26,s40,s55,s74,s98,s130],[s26,s35,s63,s74,s110,s122,s127],[s26,s40,s63,s74,s110,s122,s127],[s34,s40,s58,s74,s98,s122,s127]]
def B6_82 : List (List Sig) := [[s4,s10,s26,s35,s74,s98,s130],[s5,s10,s25,s35,s98,s122,s133],[s5,s15,s21,s40,s118,s122,s133],[s5,s21,s40,s45,s113,s122,s133],[s5,s21,s70,s85,s102,s122,s127],[s5,s21,s70,s102,s122,s125,s127],[s9,s10,s21,s35,s98,s122,s133],[s10,s26,s40,s63,s74,s98,s130],[s21,s35,s84,s91,s102,s122,s127],[s23,s40,s49,s78,s98,s122,s127],[s26,s35,s74,s94,s102,s122,s127]]
def L6 : Level := [B6_0,B6_1,B6_2,B6_3,B6_4,B6_5,B6_6,B6_7,B6_8,B6_9,B6_10,B6_11,B6_12,B6_13,B6_14,B6_15,B6_16,B6_17,B6_18,B6_19,B6_20,B6_21,B6_22,B6_23,B6_24,B6_25,B6_26,B6_27,B6_28,B6_29,B6_30,B6_31,B6_32,B6_33,B6_34,B6_35,B6_36,B6_37,B6_38,B6_39,B6_40,B6_41,B6_42,B6_43,B6_44,B6_45,B6_46,B6_47,B6_48,B6_49,B6_50,B6_51,B6_52,B6_53,B6_54,B6_55,B6_56,B6_57,B6_58,B6_59,B6_60,B6_61,B6_62,B6_63,B6_64,B6_65,B6_66,B6_67,B6_68,B6_69,B6_70,B6_71,B6_72,B6_73,B6_74,B6_75,B6_76,B6_77,B6_78,B6_79,B6_80,B6_81,B6_82]
def B7_0 : List (List Sig) := [[s1,s5,s21,s40,s49,s106,s122,s127],[s2,s5,s21,s59,s74,s102,s122,s127],[s5,s10,s20,s21,s35,s89,s122,s135],[s5,s10,s21,s35,s52,s74,s98,s130],[s5,s10,s21,s35,s63,s118,s122,s133],[s5,s10,s21,s35,s66,s98,s122,s133],[s5,s10,s21,s35,s68,s74,s98,s130],[s5,s10,s21,s45,s49,s78,s98,s130],[s5,s10,s21,s45,s49,s98,s130,s133],[s5,s10,s26,s59,s74,s106,s122,s127],[s5,s10,s31,s35,s49,s98,s125,s130],[s5,s10,s31,s35,s76,s98,s122,s127],[s5,s10,s35,s55,s82,s106,s122,s127],[s5,s10,s35,s55,s82,s109,s122,s127],[s5,s10,s35,s55,s82,s113,s122,s127],[s5,s10,s35,s55,s82,s122,s126,s127],[s5,s15,s21,s40,s74,s100,s122,s127],[s5,s15,s21,s40,s74,s115,s122,s127],[s5,s15,s21,s40,s74,s116,s122,s127],[s5,s19,s21,s40,s74,s113,s122,s127],[s5,s21,s40,s54,s74,s106,s122,s127],[s10,s26,s35,s49,s87,s98,s122,s127],[s10,s26,s35,s66,s74,s98,s122,s127]]
def B7_1 : List (List Sig) := [[s0,s5,s10,s35,s66,s74,s122,s127],[s5,s10,s21,s35,s63,s74,s122,s128],[s5,s10,s21,s35,s63,s82,s122,s135],[s5,s10,s31,s35,s49,s78,s98,s130],[s5,s10,s31,s35,s49,s98,s130,s133],[s5,s11,s21,s35,s63,s74,s122,s127],[s10,s15,s26,s35,s49,s89,s122,s135],[s10,s15,s26,s35,s55,s74,s122,s135],[s10,s15,s26,s35,s58,s74,s122,s135],[s10,s15,s26,s35,s74,s89,s122,s135],[s11,s15,s21,s35,s49,s78,s122,s127]]
def B7_2 : List (List Sig) := [[s5,s10,s15,s21,s38,s74,s98,s130],[s5,s10,s21,s40,s63,s74,s98,s130],[s5,s10,s21,s59,s63,s74,s98,s130],[s15,s21,s40,s62,s78,s98,s122,s127],[s15,s21,s40,s63,s78,s98,s122,s127],[s19,s26,s35,s49,s74,s102,s122,s127],[s26,s35,s49,s74,s102,s108,s122,s127]]
def B7_3 : List (List Sig) := [[s3,s5,s10,s21,s45,s74,s98,s130],[s5,s10,s17,s21,s35,s113,s122,s127],[s5,s10,s21,s48,s89,s98,s122,s127],[s5,s20,s21,s35,s89,s102,s122,s127],[s5,s21,s35,s40,s63,s74,s98,s130],[s5,s21,s40,s74,s94,s98,s122,s127],[s5,s21,s40,s74,s118,s122,s127],[s10,s21,s35,s78,s106,s113,s122,s127],[s15,s26,s40,s49,s74,s98,s130]]
def B7_4 : List (List Sig) := [[s0,s5,s10,s21,s59,s82,s122,s127],[s1,s5,s10,s31,s59,s98,s122,s127],[s3,s5,s10,s31,s35,s74,s98,s130],[s5,s10,s15,s21,s35,s91,s122,s135],[s5,s10,s15,s21,s36,s49,s74,s130],[s5,s10,s15,s35,s55,s74,s130,s136],[s5,s10,s16,s21,s35,s89,s122,s127],[s5,s10,s21,s35,s74,s114,s122,s127],[s5,s10,s21,s70,s74,s111,s122,s127],[s5,s10,s21,s70,s74,s118,s122,s127],[s5,s10,s34,s59,s74,s98,s122,s127],[s5,s10,s55,s70,s74,s98,s122,s127],[s5,s15,s21,s35,s89,s102,s122,s133],[s9,s10,s21,s35,s74,s98,s122,s127],[s10,s15,s26,s35,s49,s98,s130,s134],[s10,s21,s37,s49,s78,s98,s122,s127],[s10,s26,s35,s53,s82,s98,s122,s127],[s10,s26,s35,s59,s82,s98,s122,s127],[s15,s26,s35,s55,s74,s102,s122,s127],[s15,s26,s35,s58,s74,s102,s122,s127],[s15,s26,s35,s74,s89,s102,s122,s127]]
def B7_5 : List (List Sig) := [[s5,s21,s40,s49,s74,s108,s122,s127],[s5,s21,s40,s49,s82,s98,s122,s133],[s5,s31,s40,s49,s85,s98,s122,s127],[s10,s23,s35,s49,s78,s98,s122,s127],[s26,s40,s49,s74,s82,s98,s122,s127]]
def B7_6 : List (List Sig) := [[s5,s10,s15,s21,s59,s74,s102,s130],[s5,s10,s21,s35,s52,s74,s122,s135],[s5,s10,s21,s35,s63,s98,s124,s127],[s5,s10,s21,s35,s68,s74,s122,s135],[s5,s10,s21,s45,s49,s122,s133,s135],[s6,s15,s21,s40,s49,s98,s122,s127],[s15,s21,s40,s49,s86,s98,s122,s127]]
def B7_7 : List (List Sig) := [[s5,s10,s15,s35,s55,s74,s106,s130],[s5,s10,s15,s35,s55,s74,s109,s130],[s5,s10,s15,s35,s55,s74,s113,s130],[s5,s10,s15,s35,s55,s74,s126,s130],[s5,s10,s31,s35,s49,s122,s133,s135],[s5,s10,s40,s55,s74,s106,s122,s127],[s5,s10,s55,s59,s74,s106,s122,s127],[s5,s15,s21,s40,s49,s74,s123,s127],[s5,s15,s21,s40,s74,s118,s122,s127],[s5,s21,s40,s55,s74,s106,s122,s127],[s5,s21,s40,s74,s89,s106,s122,s127],[s5,s21,s40,s74,s106,s118,s122,s127],[s5,s21,s40,s74,s113,s118,s122,s127],[s7,s10,s35,s55,s74,s98,s122,s127],[s10,s20,s26,s35,s89,s98,s122,s127],[s21,s40,s49,s63,s78,s98,s122,s127],[s21,s40,s63,s74,s78,s98,s122,s127]]
def B7_8 : List (List Sig) := [[s1,s5,s10,s21,s45,s49,s98,s130],[s5,s10,s15,s21,s38,s74,s122,s135],[s5,s10,s21,s45,s54,s74,s98,s130],[s5,s10,s24,s45,s74,s98,s122,s127],[s5,s10,s31,s62,s74,s98,s122,s127],[s5,s21,s45,s49,s102,s122,s125,s127],[s10,s15,s21,s35,s78,s100,s122,s127],[s10,s15,s26,s35,s55,s98,s122,s133],[s10,s15,s26,s35,s89,s122,s127,s135],[s10,s15,s27,s35,s49,s98,s122,s127],[s10,s19,s21,s35,s78,s113,s122,s127],[s10,s21,s45,s49,s78,s109,s122,s127],[s10,s26,s35,s63,s82,s98,s122,s127]]
def B7_9 : List (List Sig) := [[s1,s5,s10,s31,s35,s49,s98,s130],[s2,s10,s26,s35,s49,s74,s98,s130],[s5,s10,s15,s21,s35,s92,s122,s135],[s5,s10,s21,s35,s49,s84,s122,s135],[s5,s10,s31,s35,s54,s74,s98,s130],[s5,s10,s31,s45,s49,s74,s98,s130],[s5,s10,s34,s35,s49,s74,s98,s130],[s5,s21,s35,s40,s63,s74,s122,s135],[s5,s21,s35,s52,s74,s102,s122,s127],[s5,s21,s35,s68,s74,s102,s122,s127],[s5,s21,s45,s49,s78,s102,s122,s127],[s10,s31,s35,s49,s78,s109,s122,s127],[s10,s31,s35,s49,s78,s122,s126,s127],[s21,s35,s49,s78,s82,s102,s122,s127]]
def B7_10 : List (List Sig) := []
def B7_11 : List (List Sig) := [[s0,s5,s10,s15,s21,s59,s74,s130],[s5,s10,s15,s35,s55,s85,s98,s130],[s5,s10,s31,s40,s89,s98,s122,s127],[s5,s10,s31,s59,s89,s98,s122,s127],[s5,s15,s21,s38,s74,s102,s122,s127],[s5,s20,s21,s40,s49,s74,s98,s130],[s5,s21,s40,s63,s74,s102,s122,s127],[s5,s21,s59,s63,s74,s102,s122,s127],[s10,s15,s26,s35,s49,s86,s98,s130],[s10,s15,s26,s35,s53,s74,s98,s130],[s10,s15,s26,s35,s59,s74,s98,s130],[s10,s15,s26,s35,s91,s98,s122,s127],[s10,s21,s35,s78,s94,s98,s122,s127],[s10,s26,s35,s63,s74,s98,s130],[s15,s21,s40,s49,s78,s102,s122,s127],[s19,s21,s40,s53,s74,s98,s122,s127]]
def B7_12 : List (List Sig) := [[s3,s5,s21,s45,s74,s102,s122,s127],[s5,s10,s15,s21,s35,s113,s122,s129],[s5,s10,s21,s35,s94,s98,s122,s135],[s5,s10,s21,s70,s82,s98,s122,s127],[s5,s10,s35,s55,s74,s106,s122,s130],[s5,s10,s35,s66,s74,s106,s122,s127],[s5,s10,s35,s66,s74,s109,s122,s127],[s5,s10,s35,s66,s74,s113,s122,s127],[s5,s10,s35,s66,s74,s122,s126,s127],[s5,s13,s21,s35,s74,s106,s122,s127],[s5,s15,s21,s40,s49,s74,s130,s135],[s5,s15,s21,s40,s49,s110,s122,s133],[s5,s21,s40,s49,s74,s111,s122,s127],[s5,s21,s40,s49,s74,s118,s122,s127],[s5,s21,s45,s74,s102,s113,s122,s127],[s15,s26,s40,s49,s74,s98,s122,s130],[s15,s26,s40,s49,s74,s110,s122,s127]]
def B7_13 : List (List Sig) := [[s5,s10,s21,s35,s52,s98,s122,s133],[s5,s10,s21,s35,s68,s98,s122,s133],[s5,s10,s21,s70,s74,s120,s122,s127],[s10,s26,s35,s52,s74,s98,s122,s127],[s10,s26,s35,s68,s74,s98,s122,s127],[s10,s26,s35,s69,s74,s98,s122,s127],[s10,s26,s45,s49,s78,s98,s122,s127],[s12,s21,s35,s49,s78,s98,s122,s127]]
def B7_14 : List (List Sig) := [[s6,s10,s21,s35,s63,s98,s122,s127],[s10,s21,s26,s35,s49,s82,s122,s135],[s10,s21,s35,s63,s86,s98,s122,s127],[s10,s26,s35,s49,s82,s98,s122,s135]]
def B7_15 : List (List Sig) := [[s2,s10,s26,s35,s49,s74,s122,s135],[s5,s10,s15,s21,s38,s98,s122,s133],[s5,s10,s15,s22,s59,s98,s122,s127],[s5,s10,s17,s35,s55,s98,s122,s127],[s5,s10,s21,s35,s63,s74,s123,s127],[s5,s10,s21,s35,s94,s102,s122,s127],[s5,s10,s21,s35,s95,s98,s122,s127],[s5,s10,s21,s40,s63,s98,s122,s133],[s5,s10,s21,s40,s82,s113,s122,s127],[s5,s10,s21,s45,s49,s89,s98,s130],[s5,s10,s21,s45,s55,s74,s98,s130],[s5,s10,s21,s45,s89,s98,s122,s130],[s5,s10,s21,s59,s82,s106,s122,s127],[s5,s10,s21,s59,s82,s109,s122,s127],[s5,s10,s21,s59,s82,s113,s122,s127],[s5,s10,s21,s59,s82,s122,s126,s127],[s5,s10,s21,s70,s74,s98,s130],[s5,s10,s35,s66,s94,s98,s122,s127],[s10,s15,s21,s35,s49,s78,s123,s127],[s10,s15,s26,s35,s63,s74,s98,s130],[s10,s15,s26,s38,s74,s98,s122,s127],[s10,s15,s35,s58,s78,s98,s122,s127],[s10,s26,s40,s63,s74,s98,s122,s127],[s10,s35,s55,s78,s84,s98,s122,s127],[s10,s35,s55,s78,s98,s106,s122,s127],[s21,s26,s40,s63,s74,s98,s122,s127]]
def B7_16 : List (List Sig) := [[s0,s5,s21,s40,s63,s74,s122,s127],[s0,s15,s21,s40,s49,s78,s122,s127],[s2,s5,s21,s40,s74,s113,s122,s127],[s5,s10,s21,s35,s51,s106,s122,s127],[s5,s10,s21,s35,s75,s113,s122,s127],[s5,s10,s21,s35,s89,s106,s122,s135],[s5,s10,s31,s35,s49,s89,s98,s130],[s5,s10,s31,s35,s55,s74,s98,s130],[s5,s10,s31,s35,s89,s98,s122,s130],[s5,s10,s35,s45,s55,s74,s98,s130],[s5,s10,s35,s66,s85,s98,s122,s127],[s5,s21,s35,s40,s63,s98,s122,s133],[s5,s21,s35,s63,s74,s102,s122,s130],[s5,s21,s40,s48,s74,s113,s122,s127],[s8,s10,s21,s35,s74,s106,s122,s127],[s10,s15,s26,s35,s92,s98,s122,s127],[s10,s21,s35,s63,s78,s98,s122,s135],[s10,s26,s35,s49,s84,s98,s122,s127],[s15,s21,s35,s49,s78,s102,s122,s130],[s26,s35,s40,s63,s74,s98,s122,s127]]
def B7_17 : List (List Sig) := [[s1,s5,s21,s45,s49,s102,s122,s127],[s5,s10,s15,s21,s36,s49,s122,s133],[s5,s10,s15,s35,s55,s85,s122,s135],[s5,s10,s21,s31,s35,s113,s122,s133],[s5,s10,s21,s35,s45,s113,s122,s133],[s5,s10,s21,s35,s49,s106,s122,s129],[s5,s20,s21,s35,s74,s115,s122,s127],[s5,s21,s45,s54,s74,s102,s122,s127],[s5,s21,s45,s74,s102,s115,s122,s127],[s10,s15,s26,s35,s49,s86,s122,s135],[s10,s15,s26,s35,s53,s74,s122,s135],[s10,s15,s26,s35,s59,s74,s122,s135],[s10,s15,s26,s36,s49,s74,s122,s127],[s10,s26,s35,s49,s82,s102,s122,s127],[s10,s26,s35,s63,s74,s122,s135]]
def B7_18 : List (List Sig) := [[s2,s26,s35,s49,s74,s102,s122,s127],[s5,s15,s21,s40,s49,s98,s125,s130],[s5,s15,s21,s40,s76,s98,s122,s127],[s5,s31,s35,s54,s74,s102,s122,s127]]
def B7_19 : List (List Sig) := [[s5,s10,s15,s21,s59,s74,s130,s136],[s5,s10,s15,s21,s70,s74,s98,s130],[s5,s15,s21,s40,s49,s78,s98,s130],[s5,s15,s21,s40,s49,s98,s130,s133],[s10,s21,s26,s35,s94,s98,s122,s127],[s10,s21,s35,s63,s78,s102,s122,s127],[s10,s35,s63,s66,s78,s98,s122,s127],[s15,s26,s40,s49,s74,s98,s127,s130],[s21,s35,s63,s78,s98,s102,s122,s127]]
def B7_20 : List (List Sig) := [[s0,s5,s10,s21,s35,s94,s122,s127],[s5,s10,s15,s22,s35,s49,s98,s130],[s5,s10,s21,s35,s49,s82,s106,s130],[s5,s10,s21,s35,s49,s82,s126,s130],[s5,s10,s21,s35,s63,s74,s130,s135],[s5,s10,s21,s35,s82,s113,s122,s130],[s5,s10,s21,s59,s82,s116,s122,s127],[s5,s10,s26,s59,s82,s98,s122,s127],[s5,s15,s35,s55,s85,s102,s122,s127],[s5,s21,s40,s54,s82,s98,s122,s127],[s5,s21,s40,s70,s74,s98,s122,s127],[s10,s19,s35,s55,s78,s98,s122,s127],[s10,s26,s35,s49,s63,s74,s98,s130],[s10,s26,s35,s63,s74,s98,s122,s130],[s15,s26,s35,s49,s86,s102,s122,s127],[s15,s26,s35,s53,s74,s102,s122,s127],[s15,s26,s35,s59,s74,s102,s122,s127],[s26,s35,s63,s74,s102,s122,s127]]
def B7_21 : List (List Sig) := [[s5,s10,s19,s21,s35,s89,s122,s135],[s5,s10,s21,s35,s74,s101,s122,s127],[s5,s10,s21,s35,s74,s118,s122,s135],[s5,s16,s21,s40,s49,s74,s122,s127],[s10,s15,s26,s35,s63,s74,s122,s135],[s10,s26,s35,s49,s88,s98,s122,s127]]
def B7_22 : List (List Sig) := [[s0,s10,s26,s35,s49,s82,s122,s127],[s3,s5,s15,s21,s40,s74,s98,s130],[s5,s10,s15,s21,s59,s74,s106,s130],[s5,s10,s15,s21,s59,s74,s109,s130],[s5,s10,s15,s21,s59,s74,s113,s130],[s5,s10,s15,s21,s59,s74,s126,s130],[s5,s10,s31,s35,s55,s74,s122,s135],[s7,s10,s21,s59,s74,s98,s122,s127]]
def B7_23 : List (List Sig) := [[s5,s21,s40,s53,s74,s106,s122,s127],[s5,s21,s40,s59,s74,s106,s122,s127],[s5,s21,s40,s72,s74,s98,s122,s127],[s5,s21,s40,s73,s74,s98,s122,s127],[s10,s26,s35,s89,s98,s106,s122,s127]]
def B7_24 : List (List Sig) := [[s0,s10,s21,s35,s63,s78,s122,s127],[s5,s10,s15,s35,s55,s98,s122,s129],[s5,s10,s18,s21,s35,s74,s98,s130],[s5,s10,s21,s37,s74,s113,s122,s127],[s5,s10,s21,s45,s49,s98,s130,s134],[s5,s10,s21,s49,s70,s74,s98,s130],[s5,s10,s21,s70,s74,s98,s122,s130],[s5,s10,s35,s55,s74,s99,s122,s127],[s5,s10,s35,s66,s74,s118,s122,s127],[s5,s10,s45,s55,s74,s102,s122,s127],[s5,s15,s21,s43,s74,s98,s122,s127],[s5,s20,s21,s40,s49,s98,s122,s133],[s5,s21,s35,s74,s102,s118,s122,s127],[s5,s21,s45,s55,s74,s102,s122,s127],[s5,s21,s45,s74,s89,s102,s122,s127],[s5,s21,s70,s74,s102,s122,s127],[s10,s15,s26,s35,s49,s74,s102,s130],[s15,s26,s35,s63,s74,s102,s122,s127],[s20,s26,s40,s49,s74,s98,s122,s127]]
def B7_25 : List (List Sig) := [[s5,s10,s15,s21,s35,s49,s74,s131],[s5,s10,s23,s35,s74,s113,s122,s127],[s5,s10,s31,s35,s49,s98,s130,s134],[s5,s15,s21,s40,s49,s122,s133,s135],[s5,s21,s48,s49,s74,s110,s122,s127],[s5,s31,s35,s55,s74,s102,s122,s127],[s15,s26,s40,s49,s74,s122,s127,s135]]
def B7_26 : List (List Sig) := [[s5,s10,s15,s21,s35,s113,s124,s127],[s5,s10,s15,s21,s59,s85,s98,s130],[s5,s10,s15,s22,s35,s49,s122,s135],[s5,s10,s15,s35,s55,s125,s126,s127],[s5,s10,s21,s35,s63,s98,s125,s130],[s10,s26,s35,s49,s63,s74,s122,s135]]
def B7_27 : List (List Sig) := [[s1,s5,s15,s21,s40,s49,s98,s130],[s5,s10,s15,s21,s59,s74,s116,s130],[s5,s10,s15,s26,s59,s74,s98,s130],[s5,s10,s15,s35,s55,s82,s98,s130],[s5,s10,s21,s35,s63,s78,s98,s130],[s5,s10,s21,s35,s63,s98,s130,s133],[s5,s10,s21,s59,s74,s106,s122,s130],[s5,s10,s40,s55,s82,s98,s122,s127],[s5,s10,s55,s59,s82,s98,s122,s127],[s5,s15,s21,s40,s54,s74,s98,s130],[s5,s15,s21,s40,s74,s117,s122,s127],[s5,s15,s21,s59,s74,s110,s122,s127],[s5,s15,s24,s40,s74,s98,s122,s127],[s5,s21,s40,s62,s74,s106,s122,s127],[s5,s21,s40,s63,s74,s106,s122,s127],[s5,s21,s40,s63,s74,s109,s122,s127],[s5,s21,s40,s63,s74,s113,s122,s127],[s5,s21,s40,s63,s74,s122,s126,s127],[s5,s21,s40,s82,s89,s98,s122,s127],[s7,s10,s21,s35,s49,s74,s98,s130],[s10,s26,s35,s63,s74,s98,s127,s130],[s15,s21,s40,s49,s78,s109,s122,s127],[s15,s21,s40,s49,s78,s122,s126,s127]]
def B7_28 : List (List Sig) := [[s5,s10,s21,s35,s98,s118,s122,s133],[s5,s10,s21,s45,s89,s122,s127,s135],[s5,s10,s21,s47,s74,s98,s122,s127],[s5,s10,s35,s55,s75,s98,s122,s127],[s5,s15,s21,s70,s74,s102,s122,s127],[s10,s19,s26,s35,s89,s98,s122,s127],[s10,s19,s35,s58,s74,s98,s122,s127],[s10,s21,s35,s70,s78,s98,s122,s127],[s10,s26,s35,s74,s98,s118,s122,s127],[s20,s21,s35,s49,s78,s102,s122,s127]]
def B7_29 : List (List Sig) := [[s0,s5,s10,s45,s55,s74,s122,s127],[s0,s10,s15,s26,s35,s49,s74,s130],[s5,s10,s21,s35,s82,s94,s122,s135],[s5,s10,s31,s35,s55,s98,s122,s133],[s5,s10,s31,s35,s89,s122,s127,s135],[s5,s10,s33,s35,s74,s98,s122,s127],[s5,s15,s22,s35,s49,s102,s122,s127],[s5,s21,s35,s63,s74,s102,s122,s133],[s15,s21,s35,s49,s78,s102,s122,s133],[s26,s35,s49,s63,s74,s102,s122,s127]]
def B7_30 : List (List Sig) := [[s5,s10,s17,s21,s59,s98,s122,s127],[s5,s10,s18,s21,s35,s74,s122,s135],[s15,s26,s35,s49,s74,s102,s122,s135]]
def B7_31 : List (List Sig) := [[s4,s5,s10,s21,s35,s74,s98,s130],[s5,s10,s15,s35,s56,s98,s122,s127],[s5,s10,s21,s31,s59,s74,s98,s130],[s5,s10,s21,s35,s49,s106,s124,s127],[s5,s10,s21,s35,s83,s98,s122,s127],[s5,s10,s21,s35,s94,s106,s122,s127],[s5,s10,s21,s35,s94,s109,s122,s127],[s5,s10,s21,s35,s94,s113,s122,s127],[s5,s10,s21,s35,s94,s122,s126,s127],[s5,s10,s21,s45,s53,s74,s98,s130],[s5,s10,s21,s45,s59,s74,s98,s130],[s5,s10,s21,s45,s91,s98,s122,s127],[s5,s10,s21,s70,s74,s98,s127,s130],[s5,s10,s26,s35,s49,s82,s122,s135],[s5,s10,s35,s55,s106,s122,s125,s127],[s5,s15,s21,s62,s74,s110,s122,s127],[s5,s21,s40,s63,s85,s98,s122,s127],[s10,s21,s35,s53,s78,s106,s122,s127],[s10,s21,s35,s72,s78,s98,s122,s127],[s15,s26,s40,s49,s98,s122,s125,s127]]
def B7_32 : List (List Sig) := [[s5,s10,s21,s35,s50,s82,s122,s127],[s5,s10,s21,s35,s63,s122,s125,s135],[s5,s10,s21,s45,s85,s113,s122,s127],[s5,s10,s31,s35,s53,s74,s98,s130],[s5,s10,s31,s35,s59,s74,s98,s130],[s5,s10,s31,s35,s91,s98,s122,s127],[s5,s10,s35,s55,s78,s106,s122,s127],[s5,s10,s35,s55,s82,s98,s122,s130],[s5,s10,s35,s55,s106,s122,s127,s133],[s5,s10,s35,s66,s82,s98,s122,s127],[s5,s13,s21,s35,s82,s98,s122,s127],[s5,s19,s21,s40,s49,s74,s98,s130],[s5,s26,s40,s63,s74,s98,s122,s127],[s15,s26,s40,s49,s78,s98,s122,s127],[s15,s26,s40,s49,s98,s122,s127,s133]]
def B7_33 : List (List Sig) := [[s5,s10,s15,s35,s55,s74,s122,s128],[s5,s10,s21,s35,s63,s78,s122,s135],[s5,s10,s21,s35,s63,s122,s133,s135],[s5,s10,s21,s35,s82,s113,s122,s133],[s5,s10,s26,s45,s74,s113,s122,s127],[s5,s10,s31,s35,s85,s113,s122,s127],[s5,s11,s15,s35,s55,s74,s122,s127],[s5,s12,s21,s35,s74,s113,s122,s127],[s5,s18,s21,s35,s74,s102,s122,s127],[s5,s21,s49,s70,s74,s102,s122,s127],[s7,s10,s21,s35,s49,s74,s122,s135],[s10,s26,s35,s49,s82,s109,s122,s127],[s10,s26,s35,s49,s82,s122,s126,s127],[s10,s26,s35,s63,s74,s122,s127,s135]]
def B7_34 : List (List Sig) := [[s5,s10,s15,s40,s55,s74,s98,s130],[s5,s10,s15,s55,s59,s74,s98,s130],[s5,s15,s21,s40,s55,s74,s98,s130],[s6,s10,s15,s21,s35,s113,s122,s127]]
def B7_35 : List (List Sig) := [[s1,s5,s10,s21,s35,s63,s98,s130],[s3,s5,s15,s21,s40,s98,s122,s133],[s3,s15,s26,s40,s74,s98,s122,s127],[s5,s10,s15,s21,s40,s113,s122,s133],[s5,s10,s15,s21,s59,s109,s122,s133],[s5,s10,s17,s21,s35,s49,s98,s130],[s5,s10,s21,s45,s63,s74,s98,s130],[s5,s10,s35,s66,s74,s98,s130],[s5,s15,s21,s40,s98,s113,s122,s133],[s5,s15,s21,s59,s85,s102,s122,s127],[s5,s21,s35,s63,s102,s122,s125,s127],[s10,s15,s24,s35,s78,s98,s122,s127],[s10,s15,s26,s59,s74,s109,s122,s127],[s10,s19,s21,s59,s78,s98,s122,s127],[s10,s21,s35,s63,s78,s109,s122,s127],[s10,s21,s35,s63,s78,s122,s126,s127],[s15,s26,s40,s74,s98,s113,s122,s127]]
def B7_36 : List (List Sig) := [[s2,s10,s35,s55,s78,s98,s122,s127],[s5,s10,s21,s35,s96,s98,s122,s127],[s5,s10,s21,s45,s92,s98,s122,s127],[s5,s10,s26,s35,s94,s98,s122,s127],[s5,s10,s31,s35,s63,s74,s98,s130],[s5,s10,s31,s38,s74,s98,s122,s127],[s5,s10,s37,s55,s74,s98,s122,s127],[s5,s14,s21,s35,s74,s98,s122,s127],[s5,s15,s21,s35,s40,s113,s122,s133],[s5,s15,s26,s59,s74,s102,s122,s127],[s5,s21,s35,s63,s78,s102,s122,s127],[s7,s21,s35,s49,s74,s102,s122,s127],[s8,s10,s21,s35,s82,s98,s122,s127],[s10,s15,s21,s35,s78,s113,s122,s135],[s10,s21,s35,s49,s79,s98,s122,s127],[s10,s26,s35,s82,s94,s98,s122,s127],[s10,s31,s40,s49,s78,s98,s122,s127],[s21,s31,s40,s49,s78,s98,s122,s127],[s21,s40,s45,s49,s78,s98,s122,s127]]
def B7_37 : List (List Sig) := [[s2,s5,s10,s21,s35,s89,s122,s135],[s4,s5,s10,s21,s35,s74,s122,s135],[s5,s10,s18,s21,s35,s98,s122,s133],[s5,s10,s21,s45,s59,s74,s122,s135],[s5,s10,s21,s70,s74,s122,s127,s135],[s5,s10,s31,s35,s92,s98,s122,s127],[s5,s10,s31,s35,s96,s98,s122,s127],[s10,s15,s26,s35,s49,s74,s130,s136],[s10,s18,s26,s35,s74,s98,s122,s127]]
def B7_38 : List (List Sig) := [[s5,s10,s15,s35,s55,s98,s124,s127],[s5,s10,s21,s35,s49,s82,s122,s136],[s5,s10,s31,s36,s49,s74,s122,s127],[s5,s21,s35,s54,s74,s108,s122,s127],[s5,s21,s35,s74,s108,s115,s122,s127]]
def B7_39 : List (List Sig) := [[s3,s15,s21,s35,s78,s102,s122,s127],[s5,s10,s15,s21,s35,s50,s74,s130],[s5,s10,s15,s21,s36,s89,s122,s127],[s5,s10,s15,s21,s59,s98,s122,s129],[s5,s10,s15,s35,s66,s74,s98,s130],[s5,s10,s21,s59,s74,s99,s122,s127],[s5,s10,s40,s66,s74,s98,s122,s127],[s5,s10,s59,s66,s74,s98,s122,s127],[s5,s13,s15,s21,s35,s74,s98,s130],[s5,s21,s40,s63,s74,s118,s122,s127],[s5,s21,s40,s66,s74,s98,s122,s127],[s6,s10,s21,s35,s49,s106,s122,s127],[s10,s26,s35,s63,s98,s122,s125,s127],[s15,s21,s35,s78,s91,s102,s122,s127],[s15,s21,s35,s78,s102,s113,s122,s127]]
def B7_40 : List (List Sig) := [[s1,s5,s10,s35,s55,s106,s122,s127],[s1,s15,s26,s40,s49,s98,s122,s127],[s4,s5,s21,s35,s74,s102,s122,s127],[s5,s10,s21,s40,s49,s106,s122,s133],[s5,s10,s26,s35,s89,s106,s122,s127],[s5,s10,s31,s59,s74,s102,s122,s127],[s5,s10,s35,s55,s92,s106,s122,s127],[s5,s10,s35,s58,s74,s106,s122,s127],[s5,s10,s45,s55,s74,s106,s122,s127],[s5,s10,s45,s55,s74,s109,s122,s127],[s5,s10,s45,s55,s74,s113,s122,s127],[s5,s10,s45,s55,s74,s122,s126,s127],[s5,s15,s21,s40,s54,s98,s122,s133],[s5,s21,s31,s59,s74,s102,s122,s127],[s5,s21,s40,s49,s98,s106,s122,s133],[s5,s21,s45,s53,s74,s102,s122,s127],[s5,s21,s45,s59,s74,s102,s122,s127],[s7,s10,s21,s35,s49,s98,s122,s133],[s10,s15,s26,s35,s49,s74,s109,s130],[s10,s15,s26,s35,s49,s74,s126,s130],[s10,s19,s21,s35,s49,s78,s98,s130],[s10,s26,s35,s63,s78,s98,s122,s127],[s10,s26,s35,s63,s98,s122,s127,s133],[s15,s26,s40,s54,s74,s98,s122,s127],[s26,s40,s49,s74,s98,s106,s122,s127]]
def B7_41 : List (List Sig) := [[s1,s5,s10,s21,s35,s63,s122,s135],[s5,s10,s15,s21,s59,s125,s126,s127],[s5,s10,s17,s21,s35,s49,s122,s135],[s5,s21,s35,s40,s49,s106,s122,s133],[s10,s21,s35,s49,s78,s106,s122,s135],[s10,s31,s35,s49,s78,s98,s122,s130]]
def B7_42 : List (List Sig) := [[s5,s10,s15,s21,s59,s82,s98,s130],[s5,s10,s21,s35,s63,s89,s98,s130]]
def B7_43 : List (List Sig) := [[s5,s10,s15,s21,s35,s51,s98,s130],[s5,s10,s21,s35,s94,s118,s122,s127],[s5,s10,s21,s59,s75,s98,s122,s127],[s5,s10,s21,s70,s98,s122,s125,s127],[s5,s10,s35,s55,s94,s98,s122,s127],[s5,s15,s21,s40,s49,s98,s130,s134],[s5,s15,s40,s55,s74,s102,s122,s127],[s5,s20,s21,s62,s74,s98,s122,s127],[s8,s10,s15,s21,s35,s74,s98,s130]]
def B7_44 : List (List Sig) := [[s1,s5,s21,s35,s63,s102,s122,s127],[s2,s10,s26,s35,s89,s98,s122,s127],[s4,s5,s10,s21,s35,s98,s122,s133],[s4,s10,s26,s35,s74,s98,s122,s127],[s5,s10,s21,s35,s85,s118,s122,s127],[s5,s10,s21,s45,s49,s74,s102,s130],[s5,s10,s21,s45,s59,s98,s122,s133],[s5,s10,s21,s46,s49,s74,s122,s127],[s5,s10,s21,s70,s78,s98,s122,s127],[s5,s10,s21,s70,s98,s122,s127,s133],[s5,s10,s31,s45,s89,s98,s122,s127],[s5,s10,s34,s35,s89,s98,s122,s127],[s5,s10,s35,s49,s66,s74,s98,s130],[s5,s10,s35,s66,s74,s98,s122,s130],[s5,s10,s45,s55,s85,s98,s122,s127],[s5,s20,s21,s35,s54,s74,s98,s130],[s5,s21,s45,s63,s74,s102,s122,s127],[s10,s15,s26,s35,s49,s85,s98,s130],[s10,s26,s45,s53,s74,s98,s122,s127],[s10,s26,s45,s59,s74,s98,s122,s127],[s15,s21,s35,s54,s78,s102,s122,s127],[s15,s21,s35,s78,s102,s115,s122,s127],[s21,s35,s49,s78,s84,s102,s122,s127],[s21,s35,s49,s78,s102,s106,s122,s127]]
def B7_45 : List (List Sig) := [[s0,s5,s10,s31,s59,s74,s122,s127],[s5,s10,s26,s35,s74,s118,s122,s127],[s5,s10,s31,s35,s49,s74,s102,s130],[s5,s10,s35,s55,s74,s108,s122,s127],[s5,s10,s35,s55,s82,s122,s127,s135],[s5,s12,s35,s55,s74,s98,s122,s127],[s5,s13,s15,s21,s35,s74,s122,s135],[s5,s19,s21,s40,s49,s98,s122,s133],[s15,s26,s35,s49,s74,s110,s122,s127],[s19,s26,s40,s49,s74,s98,s122,s127]]
def B7_46 : List (List Sig) := [[s5,s10,s15,s21,s35,s113,s125,s130],[s5,s10,s21,s35,s49,s82,s122,s128],[s5,s10,s21,s59,s106,s122,s125,s127],[s5,s11,s21,s35,s49,s82,s122,s127],[s5,s20,s21,s40,s89,s98,s122,s127],[s6,s10,s15,s35,s55,s98,s122,s127],[s10,s15,s35,s55,s86,s98,s122,s127],[s10,s15,s35,s58,s86,s98,s122,s127],[s10,s19,s21,s35,s49,s78,s122,s135]]
def B7_47 : List (List Sig) := [[s5,s10,s15,s35,s55,s74,s123,s127],[s5,s10,s21,s59,s70,s74,s98,s130],[s5,s10,s21,s59,s78,s106,s122,s127],[s5,s10,s21,s59,s82,s98,s122,s130],[s5,s10,s21,s59,s106,s122,s127,s133],[s5,s10,s35,s55,s89,s106,s122,s127],[s5,s15,s21,s40,s55,s98,s122,s133],[s5,s15,s21,s40,s89,s98,s122,s133],[s10,s21,s35,s66,s78,s98,s122,s127],[s10,s21,s35,s78,s95,s98,s122,s127],[s10,s35,s55,s63,s78,s98,s122,s127],[s15,s26,s40,s55,s74,s98,s122,s127],[s15,s26,s40,s58,s74,s98,s122,s127],[s15,s26,s40,s74,s89,s98,s122,s127]]
def B7_48 : List (List Sig) := [[s1,s10,s26,s35,s63,s98,s122,s127],[s2,s5,s21,s40,s49,s74,s98,s130],[s5,s10,s15,s21,s59,s74,s122,s128],[s5,s10,s15,s21,s60,s74,s122,s127],[s5,s10,s21,s35,s63,s89,s122,s135],[s5,s10,s21,s45,s82,s113,s122,s127],[s5,s10,s21,s48,s74,s113,s122,s127],[s5,s11,s15,s21,s59,s74,s122,s127],[s5,s21,s40,s48,s49,s74,s98,s130],[s10,s17,s26,s35,s49,s98,s122,s127],[s10,s31,s35,s66,s78,s98,s122,s127]]
def B7_49 : List (List Sig) := [[s0,s5,s10,s21,s45,s49,s74,s130],[s5,s10,s15,s21,s35,s51,s122,s135],[s5,s10,s31,s35,s82,s113,s122,s127],[s5,s15,s21,s41,s49,s74,s122,s127],[s8,s10,s15,s21,s35,s74,s122,s135],[s10,s26,s31,s35,s49,s74,s98,s130],[s10,s26,s34,s35,s49,s74,s98,s130],[s10,s26,s35,s45,s49,s74,s98,s130],[s19,s21,s35,s49,s78,s102,s122,s127],[s21,s35,s49,s78,s102,s108,s122,s127]]
def B7_50 : List (List Sig) := [[s0,s5,s10,s31,s35,s49,s74,s130],[s5,s15,s21,s40,s53,s74,s98,s130],[s5,s15,s21,s40,s59,s74,s98,s130],[s5,s20,s21,s35,s54,s74,s122,s135],[s5,s21,s40,s63,s74,s98,s130],[s10,s15,s26,s35,s49,s85,s122,s135]]
def B7_51 : List (List Sig) := [[s5,s10,s20,s35,s55,s74,s98,s130],[s5,s10,s21,s35,s49,s106,s125,s130],[s5,s10,s21,s35,s63,s98,s130,s134],[s5,s10,s21,s35,s76,s106,s122,s127],[s5,s10,s21,s63,s70,s74,s98,s130],[s5,s10,s35,s55,s66,s74,s98,s130],[s5,s10,s35,s66,s74,s98,s127,s130],[s5,s10,s35,s66,s87,s98,s122,s127],[s5,s15,s21,s40,s85,s113,s122,s127],[s10,s15,s35,s55,s78,s102,s122,s127],[s15,s21,s35,s55,s78,s102,s122,s127],[s15,s21,s35,s78,s89,s102,s122,s127]]
def B7_52 : List (List Sig) := [[s1,s5,s10,s21,s70,s98,s122,s127],[s5,s10,s15,s21,s35,s50,s122,s133],[s5,s10,s15,s35,s55,s74,s130,s135],[s5,s10,s20,s21,s35,s113,s122,s133],[s5,s10,s21,s35,s77,s98,s122,s127],[s5,s10,s21,s70,s74,s98,s122,s127],[s5,s10,s23,s59,s74,s98,s122,s127],[s5,s10,s35,s55,s74,s111,s122,s127],[s5,s10,s35,s55,s74,s118,s122,s127],[s5,s10,s45,s55,s74,s111,s122,s127],[s5,s13,s15,s21,s35,s98,s122,s133],[s5,s15,s26,s40,s74,s113,s122,s127],[s5,s21,s40,s52,s74,s98,s122,s127],[s5,s21,s40,s68,s74,s98,s122,s127],[s8,s15,s21,s35,s74,s102,s122,s127],[s13,s15,s26,s35,s74,s98,s122,s127],[s21,s40,s49,s78,s82,s98,s122,s127]]
def B7_53 : List (List Sig) := [[s5,s10,s15,s21,s59,s98,s124,s127],[s5,s10,s21,s35,s74,s119,s122,s127],[s5,s10,s21,s35,s82,s100,s122,s127],[s5,s10,s21,s35,s82,s115,s122,s127],[s5,s10,s21,s35,s82,s116,s122,s127],[s5,s10,s22,s45,s49,s98,s122,s127],[s5,s10,s31,s70,s74,s98,s122,s127],[s5,s11,s15,s21,s35,s49,s74,s130],[s5,s21,s48,s54,s74,s98,s122,s127],[s15,s26,s35,s49,s85,s102,s122,s127]]
def B7_54 : List (List Sig) := [[s5,s10,s21,s35,s49,s75,s122,s135],[s5,s15,s21,s40,s62,s74,s98,s130],[s5,s15,s21,s40,s63,s74,s98,s130]]
def B7_55 : List (List Sig) := [[s1,s5,s10,s21,s59,s106,s122,s127],[s5,s10,s21,s73,s74,s98,s122,s127],[s10,s26,s31,s35,s49,s74,s122,s135],[s10,s26,s34,s35,s49,s74,s122,s135],[s10,s26,s35,s45,s49,s74,s122,s135],[s10,s26,s35,s63,s89,s98,s122,s127]]
def B7_56 : List (List Sig) := [[s0,s10,s15,s35,s55,s78,s122,s127],[s5,s10,s21,s37,s49,s74,s98,s130],[s5,s10,s31,s40,s74,s113,s122,s127],[s5,s10,s31,s59,s74,s106,s122,s127],[s5,s10,s31,s59,s74,s109,s122,s127],[s5,s10,s31,s59,s74,s113,s122,s127],[s5,s10,s31,s59,s74,s122,s126,s127],[s5,s10,s35,s57,s74,s98,s122,s127],[s5,s15,s21,s40,s59,s74,s122,s135],[s5,s21,s31,s40,s74,s113,s122,s127],[s5,s21,s40,s45,s74,s113,s122,s127],[s5,s21,s40,s49,s82,s102,s122,s127],[s5,s21,s40,s49,s85,s106,s122,s127],[s5,s21,s59,s70,s74,s102,s122,s127],[s5,s21,s59,s74,s82,s102,s122,s127],[s8,s10,s15,s21,s35,s98,s122,s133],[s10,s15,s21,s26,s35,s89,s122,s135],[s10,s15,s26,s35,s51,s98,s122,s127],[s10,s15,s26,s35,s89,s98,s122,s135]]
def B7_57 : List (List Sig) := [[s5,s10,s21,s35,s49,s99,s122,s133],[s5,s10,s21,s45,s49,s74,s130,s136],[s5,s10,s23,s35,s49,s74,s98,s130],[s5,s10,s35,s66,s74,s122,s127,s135],[s5,s20,s21,s35,s54,s98,s122,s133],[s5,s21,s35,s49,s75,s102,s122,s127],[s5,s26,s40,s49,s74,s106,s122,s127],[s10,s15,s26,s35,s49,s98,s122,s129],[s10,s26,s35,s49,s74,s99,s122,s127],[s20,s26,s35,s54,s74,s98,s122,s127]]
def B7_58 : List (List Sig) := [[s5,s10,s15,s35,s55,s98,s125,s130],[s5,s10,s21,s40,s94,s98,s122,s127],[s5,s10,s21,s59,s94,s98,s122,s127],[s5,s10,s31,s35,s49,s74,s130,s136],[s10,s15,s21,s35,s53,s78,s98,s130],[s10,s15,s26,s35,s49,s74,s122,s136],[s26,s31,s35,s49,s74,s102,s122,s127],[s26,s34,s35,s49,s74,s102,s122,s127],[s26,s35,s45,s49,s74,s102,s122,s127]]
def B7_59 : List (List Sig) := [[s5,s10,s15,s35,s55,s78,s98,s130],[s5,s10,s15,s35,s55,s98,s130,s133],[s5,s10,s21,s62,s74,s106,s122,s127],[s5,s10,s21,s70,s89,s98,s122,s127],[s5,s21,s40,s49,s63,s74,s98,s130],[s5,s21,s40,s63,s74,s98,s122,s130],[s5,s21,s40,s63,s74,s110,s122,s127],[s10,s15,s26,s35,s49,s125,s126,s127],[s10,s15,s26,s35,s89,s102,s122,s127],[s15,s21,s40,s49,s78,s98,s122,s130],[s15,s21,s40,s49,s78,s110,s122,s127]]
def B7_60 : List (List Sig) := [[s5,s10,s21,s35,s49,s82,s123,s127],[s5,s10,s21,s35,s82,s118,s122,s127],[s5,s10,s21,s35,s94,s122,s135],[s5,s10,s21,s45,s49,s74,s106,s130],[s5,s10,s21,s45,s49,s74,s109,s130],[s5,s10,s21,s45,s49,s74,s113,s130],[s5,s10,s21,s45,s49,s74,s126,s130],[s5,s10,s21,s45,s74,s113,s122,s130],[s5,s10,s21,s59,s74,s108,s122,s127],[s5,s10,s21,s59,s82,s122,s127,s135],[s5,s10,s24,s35,s74,s106,s122,s127],[s5,s10,s31,s59,s85,s98,s122,s127],[s5,s10,s35,s58,s82,s98,s122,s127],[s5,s10,s45,s55,s82,s98,s122,s127],[s5,s10,s48,s55,s74,s98,s122,s127],[s5,s12,s21,s59,s74,s98,s122,s127],[s5,s20,s35,s55,s74,s102,s122,s127],[s5,s21,s40,s49,s74,s112,s122,s127],[s5,s21,s63,s70,s74,s102,s122,s127],[s10,s15,s26,s35,s49,s82,s98,s130],[s10,s15,s26,s35,s78,s113,s122,s127],[s10,s21,s35,s52,s78,s98,s122,s127],[s10,s21,s35,s68,s78,s98,s122,s127],[s10,s26,s40,s49,s82,s98,s122,s127]]
def B7_61 : List (List Sig) := [[s2,s5,s21,s40,s49,s98,s122,s133],[s2,s26,s40,s49,s74,s98,s122,s127],[s5,s10,s16,s35,s55,s74,s122,s127],[s5,s10,s31,s35,s49,s74,s106,s130],[s5,s10,s31,s35,s49,s74,s109,s130],[s5,s10,s31,s35,s49,s74,s113,s130],[s5,s10,s31,s35,s49,s74,s126,s130],[s5,s10,s31,s35,s74,s113,s122,s130],[s5,s10,s31,s59,s74,s116,s122,s127],[s5,s21,s40,s48,s49,s98,s122,s133],[s5,s31,s40,s54,s74,s98,s122,s127],[s6,s10,s15,s21,s59,s98,s122,s127],[s10,s26,s35,s49,s75,s98,s122,s127],[s10,s28,s35,s49,s74,s98,s122,s127],[s26,s40,s48,s49,s74,s98,s122,s127]]
def B7_62 : List (List Sig) := [[s5,s10,s15,s21,s35,s89,s113,s130],[s5,s10,s15,s21,s35,s89,s126,s130],[s5,s10,s15,s21,s59,s74,s123,s127],[s5,s10,s21,s37,s49,s74,s122,s135],[s5,s10,s21,s40,s89,s106,s122,s127],[s5,s10,s21,s59,s89,s106,s122,s127],[s7,s10,s21,s35,s89,s98,s122,s127],[s10,s15,s21,s38,s78,s98,s122,s127],[s10,s21,s40,s63,s78,s98,s122,s127],[s10,s26,s31,s35,s49,s98,s122,s133],[s10,s26,s35,s49,s82,s122,s135]]
def B7_63 : List (List Sig) := [[s5,s10,s21,s35,s94,s98,s122,s130],[s5,s10,s23,s35,s49,s74,s122,s135],[s5,s10,s35,s66,s98,s122,s125,s127],[s5,s10,s45,s55,s74,s98,s130],[s5,s15,s21,s40,s49,s74,s102,s130],[s5,s15,s21,s40,s53,s98,s122,s133],[s5,s15,s21,s40,s59,s98,s122,s133],[s5,s15,s21,s59,s74,s102,s122,s130],[s5,s15,s40,s55,s85,s98,s122,s127],[s5,s21,s40,s63,s98,s122,s133],[s15,s26,s40,s49,s86,s98,s122,s127],[s15,s26,s40,s53,s74,s98,s122,s127],[s15,s26,s40,s59,s74,s98,s122,s127],[s21,s35,s40,s63,s78,s98,s122,s127],[s26,s40,s63,s74,s98,s122,s127]]
def B7_64 : List (List Sig) := [[s0,s10,s15,s26,s35,s89,s122,s127],[s3,s10,s31,s35,s78,s98,s122,s127],[s5,s10,s15,s21,s35,s49,s98,s132],[s5,s10,s15,s21,s35,s49,s124,s135],[s5,s10,s15,s21,s35,s49,s125,s136],[s5,s10,s15,s21,s35,s94,s122,s135],[s5,s10,s21,s36,s63,s74,s122,s127],[s5,s10,s21,s45,s49,s85,s98,s130],[s5,s10,s35,s66,s78,s98,s122,s127],[s5,s10,s35,s66,s98,s122,s127,s133],[s5,s15,s21,s40,s49,s98,s122,s134],[s5,s21,s42,s49,s74,s98,s122,s127],[s10,s15,s21,s35,s53,s78,s122,s135],[s10,s15,s21,s36,s49,s78,s122,s127],[s10,s31,s35,s78,s91,s98,s122,s127],[s10,s31,s35,s78,s98,s113,s122,s127]]
def B7_65 : List (List Sig) := [[s2,s21,s35,s49,s78,s102,s122,s127],[s5,s10,s15,s35,s55,s122,s133,s135],[s5,s10,s26,s45,s49,s74,s98,s130],[s5,s10,s31,s35,s49,s85,s98,s130],[s5,s12,s21,s35,s49,s74,s98,s130],[s5,s21,s37,s49,s74,s102,s122,s127],[s5,s21,s45,s49,s74,s110,s122,s127],[s10,s26,s35,s49,s78,s106,s122,s127],[s10,s26,s35,s49,s82,s98,s122,s130]]
def B7_66 : List (List Sig) := [[s5,s10,s20,s21,s59,s74,s98,s130],[s5,s11,s15,s21,s35,s49,s122,s133],[s5,s21,s40,s63,s74,s98,s127,s130],[s5,s23,s35,s49,s74,s102,s122,s127],[s6,s10,s15,s21,s35,s49,s98,s130],[s10,s15,s26,s35,s49,s74,s122,s128],[s10,s15,s26,s35,s49,s82,s122,s135],[s10,s21,s35,s84,s91,s98,s122,s127],[s11,s15,s26,s35,s49,s74,s122,s127]]
def B7_67 : List (List Sig) := [[s1,s5,s10,s15,s35,s55,s98,s130],[s5,s10,s15,s21,s59,s74,s130,s135],[s5,s10,s15,s35,s55,s92,s98,s130],[s5,s10,s15,s35,s58,s74,s98,s130],[s5,s10,s15,s45,s55,s74,s98,s130],[s5,s10,s21,s35,s87,s113,s122,s127],[s5,s10,s21,s35,s89,s106,s122,s130],[s5,s10,s21,s40,s74,s118,s122,s127],[s5,s10,s21,s59,s74,s111,s122,s127],[s5,s10,s21,s59,s74,s118,s122,s127],[s5,s15,s21,s35,s49,s102,s124,s127],[s5,s15,s21,s40,s62,s98,s122,s133],[s5,s15,s21,s40,s63,s98,s122,s133],[s5,s21,s40,s74,s98,s118,s122,s127],[s10,s15,s26,s40,s49,s74,s98,s130],[s10,s15,s35,s55,s78,s109,s122,s127],[s10,s15,s35,s55,s78,s122,s126,s127],[s10,s21,s35,s63,s78,s98,s122,s130],[s10,s26,s35,s94,s98,s122,s127],[s15,s21,s26,s40,s49,s74,s98,s130],[s15,s21,s35,s53,s78,s102,s122,s127],[s15,s21,s35,s59,s78,s102,s122,s127],[s15,s26,s40,s62,s74,s98,s122,s127],[s15,s26,s40,s63,s74,s98,s122,s127],[s21,s35,s63,s78,s102,s122,s127]]
def B7_68 : List (List Sig) := [[s0,s5,s15,s21,s40,s49,s74,s130],[s3,s5,s10,s21,s35,s106,s122,s133],[s5,s10,s21,s35,s106,s113,s122,s133],[s5,s10,s31,s35,s87,s113,s122,s127],[s5,s21,s35,s40,s74,s118,s122,s127],[s5,s31,s40,s55,s74,s98,s122,s127],[s10,s26,s35,s74,s106,s113,s122,s127],[s15,s26,s35,s40,s49,s74,s98,s130]]
def B7_69 : List (List Sig) := [[s5,s10,s21,s35,s49,s94,s122,s135],[s5,s10,s21,s35,s74,s94,s122,s135],[s5,s10,s21,s37,s49,s98,s122,s133],[s10,s26,s37,s49,s74,s98,s122,s127],[s10,s31,s35,s54,s78,s98,s122,s127],[s10,s34,s35,s49,s78,s98,s122,s127]]
def B7_70 : List (List Sig) := [[s5,s10,s23,s35,s49,s98,s122,s133]]
def B7_71 : List (List Sig) := [[s5,s10,s21,s35,s63,s74,s102,s130],[s5,s10,s31,s35,s49,s85,s122,s135],[s5,s10,s35,s63,s66,s74,s98,s130],[s5,s12,s21,s35,s49,s74,s122,s135],[s10,s15,s26,s35,s49,s98,s124,s127],[s10,s15,s26,s35,s94,s98,s122,s127],[s10,s19,s21,s35,s53,s74,s98,s130],[s10,s19,s21,s35,s91,s98,s122,s127],[s10,s26,s35,s49,s74,s82,s122,s135],[s10,s26,s35,s63,s86,s98,s122,s127],[s15,s21,s35,s63,s78,s102,s122,s127],[s20,s21,s40,s49,s78,s98,s122,s127]]
def B7_72 : List (List Sig) := [[s1,s5,s10,s35,s66,s98,s122,s127],[s5,s10,s19,s35,s55,s74,s98,s130],[s5,s10,s21,s35,s63,s98,s122,s134],[s5,s10,s21,s35,s74,s118,s122,s130],[s5,s10,s21,s45,s49,s74,s111,s130],[s5,s10,s21,s45,s50,s74,s122,s127],[s5,s10,s35,s66,s74,s98,s122,s127],[s5,s10,s35,s66,s92,s98,s122,s127],[s5,s10,s35,s66,s96,s98,s122,s127],[s5,s10,s45,s49,s55,s74,s98,s130],[s5,s10,s45,s55,s74,s98,s122,s130],[s5,s10,s45,s66,s74,s98,s122,s127],[s5,s13,s21,s45,s74,s98,s122,s127],[s5,s15,s22,s40,s49,s98,s122,s127],[s5,s21,s35,s74,s94,s102,s122,s127],[s5,s21,s40,s49,s63,s98,s122,s133],[s5,s21,s40,s63,s74,s98,s122,s133],[s5,s21,s40,s63,s74,s122,s127,s135],[s5,s21,s40,s74,s82,s113,s122,s127],[s6,s10,s15,s21,s35,s49,s122,s135],[s15,s21,s40,s49,s78,s98,s122,s133],[s26,s40,s49,s63,s74,s98,s122,s127]]
def B7_73 : List (List Sig) := [[s5,s10,s15,s21,s35,s100,s122,s133],[s5,s10,s15,s21,s35,s115,s122,s133],[s5,s10,s15,s21,s35,s116,s122,s133],[s5,s10,s15,s21,s59,s98,s125,s130],[s5,s10,s15,s26,s35,s89,s122,s135],[s5,s10,s19,s21,s35,s113,s122,s133],[s5,s10,s21,s35,s54,s106,s122,s133],[s5,s10,s21,s45,s49,s109,s122,s133],[s5,s10,s31,s35,s50,s74,s122,s127],[s5,s13,s31,s35,s74,s98,s122,s127],[s5,s21,s45,s49,s85,s102,s122,s127],[s10,s15,s26,s35,s74,s100,s122,s127],[s10,s19,s26,s35,s74,s113,s122,s127],[s10,s26,s45,s49,s74,s109,s122,s127]]
def B7_74 : List (List Sig) := [[s5,s10,s15,s21,s59,s78,s98,s130],[s5,s10,s15,s21,s59,s98,s130,s133],[s5,s10,s15,s35,s55,s89,s98,s130],[s5,s21,s35,s49,s82,s102,s122,s133],[s5,s26,s45,s49,s74,s102,s122,s127],[s5,s31,s35,s49,s85,s102,s122,s127],[s15,s26,s35,s40,s49,s74,s122,s135],[s26,s35,s49,s74,s82,s102,s122,s127]]
def B7_75 : List (List Sig) := [[s5,s20,s21,s59,s74,s102,s122,s127],[s6,s15,s21,s35,s49,s102,s122,s127],[s10,s15,s26,s35,s89,s109,s122,s127],[s10,s15,s26,s35,s89,s122,s126,s127],[s10,s21,s26,s35,s63,s74,s98,s130],[s10,s21,s35,s78,s98,s118,s122,s127],[s15,s21,s35,s49,s86,s102,s122,s127]]
def B7_76 : List (List Sig) := [[s0,s5,s10,s21,s35,s63,s74,s130],[s5,s10,s16,s21,s59,s74,s122,s127],[s5,s10,s21,s35,s89,s94,s122,s135],[s5,s10,s21,s35,s94,s98,s122,s133],[s5,s10,s21,s35,s94,s122,s127,s135],[s5,s10,s21,s35,s118,s122,s133],[s5,s10,s21,s45,s51,s98,s122,s127],[s5,s10,s21,s59,s74,s120,s122,s127],[s5,s10,s21,s61,s74,s98,s122,s127],[s5,s10,s31,s59,s82,s98,s122,s127],[s5,s15,s21,s40,s49,s74,s130,s136],[s5,s15,s21,s40,s49,s102,s122,s133],[s5,s18,s21,s40,s74,s98,s122,s127],[s8,s10,s21,s45,s74,s98,s122,s127],[s10,s26,s35,s49,s94,s98,s122,s127],[s10,s26,s35,s74,s94,s98,s122,s127],[s10,s31,s35,s55,s78,s98,s122,s127],[s10,s31,s35,s78,s89,s98,s122,s127],[s10,s35,s45,s55,s78,s98,s122,s127],[s15,s26,s40,s49,s74,s102,s122,s127],[s21,s35,s49,s63,s78,s102,s122,s127],[s21,s35,s63,s74,s78,s102,s122,s127]]
def B7_77 : List (List Sig) := [[s5,s10,s21,s31,s35,s89,s122,s135],[s5,s10,s21,s35,s45,s89,s122,s135],[s5,s10,s21,s45,s49,s98,s122,s129],[s5,s10,s31,s35,s51,s98,s122,s127],[s5,s21,s35,s63,s74,s102,s122,s135],[s8,s10,s31,s35,s74,s98,s122,s127],[s10,s19,s21,s35,s53,s74,s122,s135],[s15,s21,s35,s49,s78,s102,s122,s135]]
def B7_78 : List (List Sig) := [[s5,s10,s21,s35,s49,s108,s122,s133],[s5,s10,s31,s35,s49,s98,s122,s129],[s5,s12,s21,s35,s49,s98,s122,s133],[s5,s21,s40,s63,s98,s122,s125,s127],[s10,s26,s35,s49,s82,s122,s127,s135],[s12,s26,s35,s49,s74,s98,s122,s127]]
def B7_79 : List (List Sig) := [[s5,s10,s21,s35,s89,s99,s122,s127],[s5,s10,s21,s45,s49,s125,s126,s127],[s5,s10,s21,s45,s89,s102,s122,s127],[s5,s10,s21,s45,s113,s122,s125,s127],[s5,s10,s21,s62,s82,s98,s122,s127],[s5,s10,s31,s59,s74,s98,s130],[s5,s10,s35,s55,s87,s98,s122,s127],[s5,s10,s35,s66,s89,s98,s122,s127],[s5,s10,s45,s55,s74,s98,s127,s130],[s5,s15,s21,s40,s49,s74,s106,s130],[s5,s15,s21,s40,s49,s74,s109,s130],[s5,s15,s21,s40,s49,s74,s113,s130],[s5,s15,s21,s40,s49,s74,s126,s130],[s5,s15,s21,s40,s74,s113,s122,s130],[s5,s21,s40,s63,s78,s98,s122,s127],[s5,s21,s40,s63,s98,s122,s127,s133],[s7,s21,s40,s49,s74,s98,s122,s127]]
def B7_80 : List (List Sig) := [[s5,s10,s15,s21,s35,s49,s123,s133],[s5,s10,s15,s21,s35,s89,s122,s136],[s5,s10,s15,s21,s35,s118,s122,s133],[s5,s10,s15,s21,s59,s122,s133,s135],[s5,s10,s21,s35,s55,s106,s122,s133],[s5,s10,s21,s35,s70,s74,s98,s130],[s5,s10,s21,s35,s89,s106,s122,s133],[s5,s10,s21,s35,s106,s118,s122,s133],[s5,s10,s21,s35,s113,s118,s122,s133],[s5,s10,s21,s45,s49,s82,s98,s130],[s5,s10,s21,s45,s70,s74,s98,s130],[s5,s10,s21,s45,s78,s113,s122,s127],[s5,s10,s21,s45,s113,s122,s127,s133],[s5,s10,s21,s48,s49,s74,s98,s130],[s5,s10,s22,s35,s63,s98,s122,s127],[s5,s10,s24,s35,s82,s98,s122,s127],[s5,s10,s31,s35,s49,s125,s126,s127],[s5,s10,s31,s35,s89,s102,s122,s127],[s5,s10,s31,s35,s113,s122,s125,s127],[s5,s20,s21,s35,s49,s74,s102,s130],[s5,s21,s48,s62,s74,s98,s122,s127],[s10,s15,s26,s35,s49,s74,s123,s127],[s10,s21,s35,s63,s78,s98,s122,s133],[s15,s21,s26,s40,s49,s98,s122,s133],[s19,s21,s35,s53,s74,s102,s122,s127]]
def B7_81 : List (List Sig) := [[s0,s5,s15,s21,s40,s49,s122,s133],[s0,s15,s26,s40,s49,s74,s122,s127],[s3,s5,s10,s21,s35,s82,s122,s135],[s5,s10,s16,s21,s35,s49,s74,s130],[s5,s10,s21,s35,s82,s113,s122,s135],[s5,s10,s31,s35,s49,s82,s98,s130],[s5,s10,s31,s35,s78,s113,s122,s127],[s5,s10,s31,s35,s113,s122,s127,s133],[s10,s21,s26,s35,s63,s74,s122,s135],[s10,s26,s35,s63,s74,s98,s122,s135],[s15,s26,s35,s49,s74,s102,s122,s130]]
def B7_82 : List (List Sig) := [[s1,s5,s10,s15,s21,s59,s98,s130],[s3,s15,s21,s40,s78,s98,s122,s127],[s5,s15,s21,s59,s102,s122,s125,s127],[s10,s15,s21,s59,s78,s109,s122,s127],[s15,s21,s40,s78,s91,s98,s122,s127],[s15,s21,s40,s78,s98,s113,s122,s127]]
def B7_83 : List (List Sig) := [[s4,s5,s21,s40,s74,s98,s122,s127],[s5,s10,s15,s31,s59,s74,s98,s130],[s5,s10,s15,s35,s55,s98,s130,s134],[s5,s10,s21,s35,s72,s74,s98,s130],[s5,s10,s21,s35,s84,s113,s122,s127],[s5,s10,s21,s35,s91,s106,s122,s127],[s5,s15,s21,s40,s49,s85,s98,s130],[s5,s15,s21,s40,s113,s122,s133],[s5,s15,s21,s59,s78,s102,s122,s127],[s10,s26,s35,s89,s94,s98,s122,s127]]
def B7_84 : List (List Sig) := [[s0,s5,s10,s21,s45,s89,s122,s127],[s5,s10,s15,s21,s35,s76,s122,s135],[s5,s10,s21,s35,s63,s74,s130,s136],[s5,s10,s21,s35,s63,s102,s122,s133],[s5,s10,s32,s35,s49,s98,s122,s127],[s5,s15,s26,s40,s49,s74,s98,s130],[s5,s21,s40,s49,s74,s106,s122,s130],[s10,s18,s21,s35,s78,s98,s122,s127],[s10,s19,s21,s35,s53,s98,s122,s133],[s10,s20,s26,s35,s49,s74,s98,s130],[s10,s26,s31,s35,s89,s98,s122,s127],[s10,s26,s34,s35,s89,s98,s122,s127],[s10,s26,s35,s45,s89,s98,s122,s127],[s10,s26,s35,s63,s74,s102,s122,s127],[s10,s34,s35,s58,s74,s98,s122,s127],[s21,s26,s35,s63,s74,s102,s122,s127],[s26,s35,s63,s74,s98,s102,s122,s127]]
def B7_85 : List (List Sig) := [[s0,s5,s10,s31,s35,s89,s122,s127],[s5,s10,s21,s35,s49,s111,s122,s133],[s5,s10,s21,s35,s49,s118,s122,s133],[s5,s10,s21,s35,s64,s74,s122,s127],[s5,s10,s21,s35,s74,s118,s122,s133],[s5,s10,s35,s69,s74,s98,s122,s127],[s5,s10,s45,s55,s74,s122,s127,s135],[s10,s15,s26,s35,s49,s74,s130,s135]]
def B7_86 : List (List Sig) := [[s5,s10,s15,s21,s62,s74,s98,s130],[s5,s10,s21,s35,s54,s82,s122,s135],[s5,s10,s21,s35,s70,s74,s122,s135],[s5,s10,s21,s45,s49,s74,s122,s128],[s5,s11,s21,s45,s49,s74,s122,s127],[s5,s21,s35,s49,s74,s103,s122,s127]]
def B7_87 : List (List Sig) := [[s1,s5,s21,s40,s63,s98,s122,s127],[s5,s10,s15,s24,s35,s74,s98,s130],[s5,s10,s19,s21,s59,s74,s98,s130],[s5,s10,s21,s35,s63,s74,s106,s130],[s5,s10,s21,s35,s63,s74,s109,s130],[s5,s10,s21,s35,s63,s74,s113,s130],[s5,s10,s21,s35,s63,s74,s126,s130],[s5,s10,s21,s38,s74,s106,s122,s127],[s5,s10,s21,s39,s74,s98,s122,s127],[s5,s10,s31,s35,s49,s74,s122,s128],[s5,s11,s31,s35,s49,s74,s122,s127],[s5,s15,s21,s35,s49,s102,s125,s130],[s5,s15,s21,s35,s76,s102,s122,s127],[s10,s15,s21,s35,s49,s78,s126,s130],[s10,s15,s26,s59,s78,s98,s122,s127],[s15,s21,s40,s54,s78,s98,s122,s127],[s21,s40,s49,s78,s84,s98,s122,s127],[s21,s40,s49,s78,s98,s106,s122,s127]]
def B7_88 : List (List Sig) := [[s1,s5,s10,s21,s45,s113,s122,s127],[s2,s5,s10,s35,s55,s74,s98,s130],[s3,s10,s26,s35,s82,s98,s122,s127],[s5,s10,s15,s21,s35,s89,s122,s128],[s5,s10,s21,s35,s92,s106,s122,s127],[s5,s10,s21,s70,s74,s102,s122,s127],[s5,s10,s31,s40,s49,s74,s98,s130],[s5,s10,s31,s49,s59,s74,s98,s130],[s5,s10,s31,s59,s74,s98,s122,s130],[s5,s10,s66,s70,s74,s98,s122,s127],[s5,s11,s15,s21,s35,s89,s122,s127],[s5,s15,s21,s35,s74,s104,s122,s127],[s5,s21,s31,s40,s49,s74,s98,s130],[s5,s21,s40,s45,s49,s74,s98,s130],[s5,s21,s40,s49,s106,s122,s133],[s5,s21,s70,s74,s98,s102,s122,s127],[s10,s21,s26,s35,s63,s98,s122,s133],[s10,s26,s35,s82,s98,s113,s122,s127]]
def B7_89 : List (List Sig) := [[s0,s5,s10,s21,s35,s63,s122,s133],[s0,s10,s26,s35,s63,s74,s122,s127],[s1,s5,s10,s31,s35,s113,s122,s127],[s2,s5,s10,s21,s35,s113,s122,s133],[s5,s10,s15,s21,s35,s49,s134,s136],[s5,s10,s15,s21,s59,s89,s98,s130],[s5,s10,s21,s35,s72,s74,s122,s135],[s5,s10,s31,s45,s74,s113,s122,s127],[s5,s10,s34,s35,s74,s113,s122,s127],[s5,s21,s35,s54,s82,s102,s122,s127],[s5,s21,s35,s70,s74,s102,s122,s127],[s5,s21,s35,s74,s102,s119,s122,s127],[s5,s21,s45,s70,s74,s102,s122,s127],[s5,s21,s48,s49,s74,s102,s122,s127]]
def B7_90 : List (List Sig) := [[s5,s10,s21,s35,s63,s94,s98,s130],[s10,s20,s26,s35,s49,s74,s122,s135]]
def B7_91 : List (List Sig) := [[s1,s5,s15,s21,s59,s102,s122,s127],[s4,s10,s21,s35,s78,s98,s122,s127],[s5,s10,s21,s35,s63,s85,s98,s130],[s5,s10,s21,s35,s94,s98,s122,s127],[s5,s10,s21,s35,s118,s122,s125,s127],[s5,s10,s21,s37,s89,s98,s122,s127],[s5,s10,s21,s45,s49,s98,s124,s127],[s5,s10,s21,s45,s94,s98,s122,s127],[s5,s10,s45,s55,s98,s122,s125,s127],[s5,s15,s21,s40,s50,s74,s122,s127],[s5,s20,s21,s40,s74,s113,s122,s127],[s5,s21,s59,s74,s102,s106,s122,s127],[s10,s15,s26,s35,s49,s98,s125,s130],[s10,s15,s26,s35,s76,s98,s122,s127],[s10,s15,s29,s35,s74,s98,s122,s127],[s10,s21,s45,s53,s78,s98,s122,s127],[s10,s21,s45,s59,s78,s98,s122,s127]]
def B7_92 : List (List Sig) := [[s5,s10,s15,s21,s35,s49,s126,s134],[s5,s10,s15,s21,s35,s113,s122,s134],[s5,s10,s21,s35,s78,s118,s122,s127],[s5,s10,s21,s35,s118,s122,s127,s133],[s5,s10,s23,s35,s89,s98,s122,s127],[s5,s10,s26,s35,s63,s74,s98,s130],[s5,s10,s31,s35,s49,s98,s124,s127],[s5,s10,s31,s35,s94,s98,s122,s127],[s5,s10,s45,s55,s78,s98,s122,s127],[s5,s10,s45,s55,s98,s122,s127,s133],[s5,s15,s21,s40,s49,s106,s122,s133],[s5,s15,s21,s40,s49,s109,s122,s133],[s5,s15,s21,s40,s49,s113,s122,s133],[s5,s15,s21,s40,s49,s122,s126,s133],[s5,s15,s21,s40,s74,s113,s122,s133],[s5,s21,s35,s63,s74,s110,s122,s127],[s5,s21,s35,s72,s74,s102,s122,s127],[s10,s15,s26,s35,s49,s78,s98,s130],[s10,s15,s26,s35,s49,s98,s130,s133],[s10,s31,s35,s53,s78,s98,s122,s127],[s10,s31,s35,s59,s78,s98,s122,s127],[s10,s35,s55,s78,s82,s98,s122,s127],[s15,s21,s35,s49,s78,s110,s122,s127],[s15,s26,s40,s49,s74,s109,s122,s127],[s15,s26,s40,s49,s74,s122,s126,s127],[s19,s21,s40,s49,s78,s98,s122,s127]]
def B7_93 : List (List Sig) := [[s0,s5,s10,s21,s70,s74,s122,s127],[s5,s10,s15,s24,s35,s74,s122,s135],[s5,s10,s21,s35,s55,s82,s122,s135],[s5,s10,s21,s35,s70,s98,s122,s133],[s5,s10,s21,s35,s82,s89,s122,s135],[s5,s10,s21,s45,s74,s100,s122,s127],[s5,s10,s21,s45,s74,s115,s122,s127],[s5,s10,s21,s45,s74,s116,s122,s127],[s5,s20,s21,s35,s49,s102,s122,s133],[s10,s26,s35,s54,s82,s98,s122,s127],[s10,s26,s35,s70,s74,s98,s122,s127],[s20,s26,s35,s49,s74,s102,s122,s127]]
def B7_94 : List (List Sig) := [[s5,s10,s16,s21,s35,s49,s122,s133],[s5,s10,s21,s59,s87,s98,s122,s127],[s5,s10,s31,s35,s74,s100,s122,s127],[s5,s10,s31,s35,s74,s115,s122,s127],[s5,s10,s31,s35,s74,s116,s122,s127],[s5,s21,s40,s45,s49,s74,s122,s135],[s10,s15,s21,s35,s80,s98,s122,s127],[s10,s15,s40,s55,s78,s98,s122,s127],[s10,s21,s35,s53,s84,s98,s122,s127],[s15,s21,s40,s55,s78,s98,s122,s127],[s15,s21,s40,s78,s89,s98,s122,s127]]
def B7_95 : List (List Sig) := [[s3,s10,s15,s26,s35,s74,s98,s130],[s5,s10,s21,s45,s89,s106,s122,s127],[s5,s10,s21,s45,s89,s109,s122,s127],[s5,s10,s21,s45,s89,s113,s122,s127],[s5,s10,s21,s45,s89,s122,s126,s127],[s5,s10,s31,s59,s74,s98,s127,s130],[s5,s10,s31,s59,s87,s98,s122,s127],[s5,s10,s35,s55,s84,s98,s122,s127],[s5,s15,s21,s62,s74,s102,s122,s127],[s8,s15,s21,s40,s74,s98,s122,s127],[s10,s35,s66,s78,s98,s122,s127]]
def B7_96 : List (List Sig) := [[s5,s10,s15,s36,s55,s74,s122,s127],[s5,s10,s21,s35,s53,s106,s122,s133],[s5,s10,s21,s35,s59,s106,s122,s133],[s5,s10,s21,s35,s63,s94,s122,s135],[s5,s10,s21,s35,s72,s98,s122,s133],[s5,s10,s31,s35,s89,s106,s122,s127],[s5,s10,s31,s35,s89,s109,s122,s127],[s5,s10,s31,s35,s89,s113,s122,s127],[s5,s10,s31,s35,s89,s122,s126,s127],[s5,s10,s35,s55,s82,s102,s122,s127],[s5,s10,s35,s55,s85,s106,s122,s127],[s5,s15,s21,s35,s54,s74,s102,s130],[s5,s15,s21,s40,s49,s98,s122,s129],[s5,s15,s24,s35,s74,s102,s122,s127],[s5,s19,s21,s59,s74,s102,s122,s127],[s5,s21,s35,s82,s89,s102,s122,s127],[s5,s21,s40,s49,s74,s99,s122,s127],[s5,s21,s59,s74,s102,s108,s122,s127],[s10,s26,s35,s53,s74,s106,s122,s127],[s10,s26,s35,s72,s74,s98,s122,s127],[s10,s31,s35,s63,s78,s98,s122,s127],[s15,s26,s40,s49,s85,s98,s122,s127]]
def B7_97 : List (List Sig) := [[s5,s10,s21,s35,s49,s106,s122,s134],[s5,s10,s21,s35,s63,s85,s122,s135],[s5,s21,s40,s49,s74,s106,s122,s133],[s5,s31,s40,s49,s74,s102,s122,s127],[s10,s15,s26,s35,s49,s122,s125,s135]]
def B7_98 : List (List Sig) := [[s5,s10,s15,s21,s59,s98,s130,s134],[s5,s10,s26,s35,s63,s74,s122,s135],[s5,s15,s21,s40,s49,s125,s126,s127],[s5,s15,s21,s40,s89,s102,s122,s127],[s5,s15,s21,s40,s113,s122,s125,s127],[s10,s15,s26,s35,s49,s78,s122,s135],[s10,s15,s26,s35,s49,s122,s133,s135]]
def B7_99 : List (List Sig) := [[s5,s10,s21,s35,s63,s74,s118,s130],[s5,s10,s21,s35,s66,s74,s98,s130],[s5,s10,s35,s55,s63,s74,s98,s130],[s5,s15,s21,s40,s78,s113,s122,s127],[s5,s15,s21,s40,s113,s122,s127,s133],[s6,s10,s21,s45,s49,s98,s122,s127],[s10,s15,s35,s55,s78,s98,s122,s130],[s10,s15,s35,s66,s78,s98,s122,s127],[s13,s15,s21,s35,s78,s98,s122,s127]]
def B7_100 : List (List Sig) := [[s1,s5,s10,s21,s35,s118,s122,s127],[s1,s5,s10,s45,s55,s98,s122,s127],[s1,s10,s15,s26,s35,s49,s98,s130],[s5,s10,s15,s22,s35,s113,s122,s127],[s5,s10,s15,s24,s35,s98,s122,s133],[s5,s10,s21,s35,s63,s106,s122,s133],[s5,s10,s21,s35,s63,s109,s122,s133],[s5,s10,s21,s35,s63,s113,s122,s133],[s5,s10,s21,s35,s63,s122,s126,s133],[s5,s10,s21,s35,s74,s107,s122,s127],[s5,s10,s21,s35,s74,s118,s122,s127],[s5,s10,s21,s35,s89,s108,s122,s127],[s5,s10,s21,s45,s49,s74,s123,s127],[s5,s10,s21,s45,s74,s118,s122,s127],[s5,s10,s25,s35,s74,s98,s122,s127],[s5,s10,s26,s45,s89,s98,s122,s127],[s5,s10,s31,s35,s49,s87,s98,s130],[s5,s10,s31,s35,s66,s74,s98,s130],[s5,s10,s35,s55,s96,s98,s122,s127],[s5,s10,s45,s55,s92,s98,s122,s127],[s5,s10,s45,s58,s74,s98,s122,s127],[s5,s12,s21,s35,s89,s98,s122,s127],[s5,s21,s35,s63,s85,s102,s122,s127],[s5,s21,s40,s49,s75,s98,s122,s127],[s6,s10,s31,s35,s49,s98,s122,s127],[s10,s15,s26,s35,s54,s74,s98,s130],[s10,s19,s26,s59,s74,s98,s122,s127],[s10,s26,s35,s55,s82,s98,s122,s127],[s10,s26,s35,s58,s82,s98,s122,s127],[s10,s26,s35,s63,s74,s109,s122,s127],[s10,s26,s35,s63,s74,s122,s126,s127],[s10,s26,s35,s82,s89,s98,s122,s127],[s10,s31,s35,s49,s86,s98,s122,s127],[s10,s34,s35,s49,s86,s98,s122,s127],[s10,s34,s35,s53,s74,s98,s122,s127],[s15,s26,s35,s49,s102,s122,s125,s127]]
def B7_101 : List (List Sig) := [[s0,s5,s10,s35,s55,s82,s122,s127],[s3,s10,s15,s26,s35,s74,s122,s135],[s5,s10,s31,s35,s49,s74,s123,s127],[s5,s10,s31,s35,s74,s118,s122,s127],[s5,s10,s31,s59,s74,s122,s127,s135],[s5,s21,s31,s40,s49,s98,s122,s133],[s5,s21,s40,s45,s49,s98,s122,s133],[s5,s21,s45,s49,s74,s102,s122,s130],[s5,s26,s35,s63,s74,s102,s122,s127],[s10,s15,s26,s35,s74,s113,s122,s135],[s15,s26,s35,s49,s78,s102,s122,s127],[s26,s31,s40,s49,s74,s98,s122,s127],[s26,s34,s40,s49,s74,s98,s122,s127],[s26,s40,s45,s49,s74,s98,s122,s127]]
def B7_102 : List (List Sig) := [[s5,s10,s15,s21,s35,s89,s123,s127],[s10,s15,s26,s40,s89,s98,s122,s127]]
def B7_103 : List (List Sig) := [[s2,s5,s10,s21,s59,s74,s98,s130],[s5,s10,s15,s35,s55,s74,s102,s130],[s5,s20,s40,s55,s74,s98,s122,s127],[s5,s21,s40,s49,s106,s122,s125,s127],[s10,s26,s35,s63,s94,s98,s122,s127]]
def B7_104 : List (List Sig) := [[s3,s15,s26,s35,s74,s102,s122,s127],[s5,s10,s21,s35,s63,s98,s122,s129],[s5,s10,s21,s70,s74,s106,s122,s127],[s5,s10,s21,s70,s74,s109,s122,s127],[s5,s10,s21,s70,s74,s113,s122,s127],[s5,s10,s21,s70,s74,s122,s126,s127],[s5,s21,s40,s49,s78,s106,s122,s127],[s5,s21,s40,s49,s106,s122,s127,s133],[s10,s15,s26,s35,s89,s122,s135],[s10,s21,s35,s49,s78,s99,s122,s127],[s10,s26,s35,s63,s85,s98,s122,s127],[s10,s35,s49,s66,s78,s98,s122,s127],[s10,s35,s66,s74,s78,s98,s122,s127],[s15,s26,s35,s74,s102,s113,s122,s127],[s20,s21,s35,s54,s78,s98,s122,s127]]
def B7_105 : List (List Sig) := [[s5,s10,s21,s35,s49,s87,s122,s135],[s5,s10,s21,s35,s63,s74,s122,s136],[s5,s10,s21,s35,s66,s74,s122,s135],[s5,s10,s21,s45,s49,s74,s130,s135],[s5,s10,s22,s35,s49,s106,s122,s127],[s5,s10,s26,s35,s82,s113,s122,s127],[s5,s15,s21,s40,s49,s74,s122,s128],[s10,s19,s26,s35,s49,s74,s98,s130],[s10,s31,s35,s49,s78,s102,s122,s127],[s21,s31,s35,s49,s78,s102,s122,s127],[s21,s35,s45,s49,s78,s102,s122,s127]]
def B7_106 : List (List Sig) := [[s1,s10,s15,s26,s35,s49,s122,s135],[s5,s10,s21,s35,s63,s125,s126,s127],[s5,s10,s31,s35,s49,s74,s130,s135],[s10,s15,s26,s35,s54,s74,s122,s135],[s10,s26,s35,s49,s74,s106,s122,s135]]
def B7_107 : List (List Sig) := [[s1,s5,s15,s21,s40,s113,s122,s127],[s3,s5,s21,s40,s74,s106,s122,s127],[s5,s10,s21,s35,s63,s82,s98,s130],[s5,s10,s21,s35,s89,s111,s122,s127],[s5,s10,s21,s35,s89,s118,s122,s127],[s5,s10,s21,s38,s82,s98,s122,s127],[s5,s10,s21,s45,s89,s111,s122,s127],[s5,s10,s21,s70,s94,s98,s122,s127],[s5,s10,s31,s59,s98,s122,s125,s127],[s5,s10,s45,s55,s89,s98,s122,s127],[s5,s21,s40,s74,s106,s113,s122,s127],[s7,s10,s21,s35,s74,s113,s122,s127],[s10,s15,s26,s35,s49,s89,s98,s130],[s10,s15,s26,s35,s55,s74,s98,s130],[s10,s15,s26,s35,s58,s74,s98,s130],[s10,s15,s26,s35,s89,s98,s122,s130],[s10,s15,s26,s35,s93,s98,s122,s127]]
def B7_108 : List (List Sig) := [[s0,s5,s10,s15,s35,s55,s74,s130],[s2,s21,s40,s49,s78,s98,s122,s127],[s5,s10,s21,s35,s65,s98,s122,s127],[s5,s10,s21,s35,s90,s98,s122,s127],[s5,s10,s21,s70,s85,s98,s122,s127],[s5,s10,s31,s59,s78,s98,s122,s127],[s5,s10,s31,s59,s98,s122,s127,s133],[s5,s10,s35,s66,s74,s102,s122,s127],[s5,s21,s35,s66,s74,s102,s122,s127],[s21,s40,s48,s49,s78,s98,s122,s127]]
def B7_109 : List (List Sig) := [[s1,s15,s26,s35,s49,s102,s122,s127],[s5,s10,s21,s35,s53,s82,s122,s135],[s5,s10,s21,s35,s59,s82,s122,s135],[s5,s10,s21,s35,s74,s120,s122,s127],[s5,s10,s21,s36,s49,s82,s122,s127],[s5,s10,s21,s45,s74,s120,s122,s127],[s5,s10,s21,s70,s74,s116,s122,s127],[s5,s10,s26,s70,s74,s98,s122,s127],[s5,s15,s21,s35,s54,s102,s122,s133],[s5,s23,s40,s49,s74,s98,s122,s127],[s15,s26,s35,s54,s74,s102,s122,s127],[s15,s26,s35,s74,s102,s115,s122,s127],[s26,s35,s49,s74,s102,s106,s122,s127]]
def B7_110 : List (List Sig) := [[s0,s10,s31,s35,s49,s78,s122,s127],[s5,s10,s21,s59,s84,s98,s122,s127],[s5,s15,s21,s40,s49,s98,s124,s127],[s15,s21,s40,s53,s78,s98,s122,s127],[s15,s21,s40,s59,s78,s98,s122,s127],[s21,s40,s63,s78,s98,s122,s127]]
def B7_111 : List (List Sig) := [[s5,s10,s21,s45,s49,s98,s125,s130],[s5,s10,s21,s45,s76,s98,s122,s127],[s5,s10,s21,s59,s82,s102,s122,s127],[s5,s10,s21,s59,s85,s106,s122,s127],[s5,s15,s21,s40,s49,s74,s110,s130],[s10,s19,s26,s35,s49,s74,s122,s135],[s10,s20,s35,s55,s78,s98,s122,s127],[s10,s35,s55,s66,s78,s98,s122,s127]]
def L7 : Level := [B7_0,B7_1,B7_2,B7_3,B7_4,B7_5,B7_6,B7_7,B7_8,B7_9,B7_10,B7_11,B7_12,B7_13,B7_14,B7_15,B7_16,B7_17,B7_18,B7_19,B7_20,B7_21,B7_22,B7_23,B7_24,B7_25,B7_26,B7_27,B7_28,B7_29,B7_30,B7_31,B7_32,B7_33,B7_34,B7_35,B7_36,B7_37,B7_38,B7_39,B7_40,B7_41,B7_42,B7_43,B7_44,B7_45,B7_46,B7_47,B7_48,B7_49,B7_50,B7_51,B7_52,B7_53,B7_54,B7_55,B7_56,B7_57,B7_58,B7_59,B7_60,B7_61,B7_62,B7_63,B7_64,B7_65,B7_66,B7_67,B7_68,B7_69,B7_70,B7_71,B7_72,B7_73,B7_74,B7_75,B7_76,B7_77,B7_78,B7_79,B7_80,B7_81,B7_82,B7_83,B7_84,B7_85,B7_86,B7_87,B7_88,B7_89,B7_90,B7_91,B7_92,B7_93,B7_94,B7_95,B7_96,B7_97,B7_98,B7_99,B7_100,B7_101,B7_102,B7_103,B7_104,B7_105,B7_106,B7_107,B7_108,B7_109,B7_110,B7_111]
def B8_0 : List (List Sig) := [[s1,s5,s10,s15,s21,s35,s113,s122,s127],[s3,s10,s15,s26,s35,s74,s98,s122,s127],[s5,s10,s15,s21,s35,s49,s74,s113,s130],[s5,s10,s15,s21,s35,s53,s98,s122,s133],[s5,s10,s15,s21,s35,s82,s113,s122,s127],[s5,s10,s15,s35,s55,s74,s113,s122,s127],[s5,s10,s19,s21,s35,s49,s98,s122,s133],[s5,s10,s21,s35,s49,s82,s122,s127,s135],[s5,s10,s21,s35,s82,s98,s113,s122,s127],[s10,s26,s35,s49,s74,s82,s98,s122,s127],[s15,s21,s35,s49,s78,s102,s122,s127]]
def B8_1 : List (List Sig) := [[s3,s5,s10,s15,s21,s35,s74,s98,s130],[s5,s10,s15,s26,s35,s49,s74,s98,s130],[s5,s10,s21,s35,s49,s82,s109,s122,s127],[s5,s10,s35,s49,s55,s82,s98,s122,s127],[s5,s10,s35,s55,s74,s82,s98,s122,s127],[s5,s15,s21,s40,s74,s89,s98,s122,s127]]
def B8_2 : List (List Sig) := [[s5,s10,s15,s21,s59,s74,s116,s122,s127],[s5,s10,s15,s35,s66,s74,s98,s122,s127],[s5,s10,s19,s21,s59,s74,s98,s122,s127],[s5,s10,s21,s40,s49,s74,s106,s122,s127],[s5,s10,s21,s45,s53,s74,s98,s122,s127],[s5,s10,s21,s59,s70,s74,s98,s122,s127],[s5,s10,s31,s35,s49,s74,s113,s122,s127],[s5,s10,s34,s35,s49,s74,s98,s122,s127],[s5,s10,s35,s55,s74,s106,s122,s127],[s5,s15,s21,s35,s53,s74,s102,s122,s127],[s5,s15,s21,s40,s49,s74,s106,s122,s127],[s5,s15,s21,s40,s49,s85,s98,s122,s127],[s5,s19,s21,s35,s49,s74,s102,s122,s127],[s5,s21,s40,s49,s74,s98,s106,s122,s127],[s10,s15,s26,s35,s49,s74,s98,s122,s135],[s15,s21,s26,s40,s49,s74,s98,s122,s127]]
def B8_3 : List (List Sig) := [[s3,s5,s10,s15,s21,s35,s74,s122,s135],[s3,s5,s10,s31,s35,s74,s98,s122,s127],[s5,s10,s15,s21,s35,s89,s106,s122,s127],[s5,s10,s15,s21,s62,s74,s98,s122,s127],[s5,s10,s15,s26,s35,s49,s74,s122,s135],[s5,s10,s15,s31,s35,s49,s74,s98,s130],[s5,s10,s21,s35,s49,s74,s82,s122,s135],[s5,s10,s21,s35,s54,s74,s106,s122,s127],[s5,s10,s21,s35,s89,s98,s106,s122,s127],[s5,s15,s21,s40,s55,s74,s98,s122,s127],[s10,s15,s21,s26,s35,s89,s98,s122,s127]]
def B8_4 : List (List Sig) := [[s5,s10,s15,s24,s35,s74,s98,s122,s127],[s5,s10,s21,s35,s74,s118,s122,s127],[s10,s26,s35,s63,s74,s98,s122,s127],[s15,s21,s35,s40,s49,s78,s98,s122,s127],[s15,s21,s40,s49,s74,s78,s98,s122,s127]]
def B8_5 : List (List Sig) := [[s2,s5,s21,s40,s49,s74,s98,s122,s127],[s5,s10,s15,s21,s35,s74,s115,s122,s127],[s5,s10,s15,s21,s35,s74,s116,s122,s127],[s5,s10,s19,s21,s35,s74,s113,s122,s127],[s5,s10,s21,s35,s49,s74,s99,s122,s127],[s5,s10,s21,s35,s49,s106,s122,s127,s133],[s5,s10,s21,s35,s52,s74,s98,s122,s127],[s5,s10,s21,s35,s63,s74,s98,s130],[s5,s10,s21,s35,s70,s74,s98,s122,s127],[s5,s10,s21,s40,s63,s74,s98,s122,s127],[s5,s10,s21,s49,s70,s74,s98,s122,s127],[s5,s15,s21,s40,s63,s74,s98,s122,s127],[s5,s21,s31,s40,s49,s74,s98,s122,s127],[s10,s15,s21,s35,s78,s89,s98,s122,s127],[s10,s15,s26,s35,s49,s74,s122,s126,s127]]
def B8_6 : List (List Sig) := [[s2,s5,s10,s21,s35,s89,s98,s122,s127],[s5,s10,s15,s21,s35,s49,s74,s122,s128],[s5,s10,s15,s21,s35,s49,s74,s126,s130],[s5,s10,s15,s21,s40,s49,s98,s122,s133],[s5,s10,s15,s35,s55,s74,s122,s126,s127],[s5,s10,s21,s31,s35,s89,s98,s122,s127],[s5,s10,s21,s35,s53,s82,s98,s122,s127],[s5,s15,s21,s40,s49,s74,s98,s122,s130],[s10,s21,s35,s49,s78,s98,s106,s122,s127]]
def B8_7 : List (List Sig) := [[s0,s5,s10,s21,s35,s63,s74,s122,s127],[s5,s10,s15,s21,s35,s54,s98,s122,s133],[s5,s10,s15,s21,s35,s89,s98,s122,s130],[s5,s10,s20,s21,s35,s49,s98,s122,s133],[s5,s10,s21,s35,s49,s78,s106,s122,s127],[s5,s10,s21,s35,s63,s74,s122,s135],[s5,s21,s40,s48,s49,s74,s98,s122,s127],[s10,s15,s21,s35,s55,s78,s98,s122,s127],[s15,s26,s35,s49,s74,s102,s122,s127]]
def B8_8 : List (List Sig) := [[s0,s5,s10,s15,s21,s35,s49,s122,s133],[s5,s10,s15,s21,s59,s74,s98,s130],[s5,s10,s21,s35,s49,s74,s106,s122,s133],[s5,s10,s21,s35,s63,s98,s122,s127,s133],[s5,s10,s21,s45,s49,s74,s98,s130],[s5,s10,s31,s35,s49,s74,s122,s126,s127],[s5,s10,s45,s55,s74,s98,s122,s127],[s5,s15,s21,s40,s49,s74,s102,s122,s127],[s5,s21,s35,s49,s74,s102,s108,s122,s127]]
def B8_9 : List (List Sig) := [[s2,s10,s21,s35,s49,s78,s98,s122,s127],[s5,s10,s15,s21,s35,s89,s102,s122,s127],[s5,s10,s15,s21,s45,s89,s98,s122,s127],[s5,s10,s20,s21,s59,s74,s98,s122,s127],[s5,s10,s21,s45,s54,s74,s98,s122,s127],[s5,s15,s21,s35,s54,s74,s102,s122,s127],[s5,s15,s21,s40,s49,s74,s98,s127,s130],[s5,s20,s21,s35,s49,s74,s102,s122,s127],[s6,s10,s15,s21,s35,s49,s98,s122,s127],[s10,s15,s21,s35,s63,s78,s98,s122,s127],[s10,s21,s31,s35,s49,s78,s98,s122,s127]]
def B8_10 : List (List Sig) := [[s0,s5,s10,s15,s21,s59,s74,s122,s127],[s0,s5,s10,s21,s45,s49,s74,s122,s127],[s4,s5,s10,s21,s35,s74,s98,s122,s127],[s5,s10,s21,s35,s49,s106,s122,s125,s127],[s5,s10,s21,s35,s59,s74,s106,s122,s127],[s5,s10,s21,s35,s63,s74,s118,s122,s127],[s5,s10,s21,s35,s63,s78,s98,s122,s127],[s5,s10,s21,s49,s59,s74,s106,s122,s127],[s5,s10,s31,s59,s74,s98,s122,s127],[s10,s15,s21,s35,s49,s78,s98,s122,s130],[s10,s19,s21,s35,s53,s74,s98,s122,s127]]
def B8_11 : List (List Sig) := [[s5,s10,s15,s21,s36,s49,s74,s122,s127],[s5,s10,s15,s21,s40,s74,s113,s122,s127],[s5,s10,s15,s21,s59,s98,s122,s127,s133],[s5,s10,s21,s35,s49,s63,s98,s122,s133],[s5,s10,s21,s35,s49,s74,s111,s122,s127],[s5,s10,s21,s35,s63,s74,s98,s122,s133],[s5,s10,s21,s45,s49,s98,s122,s127,s133],[s5,s15,s21,s40,s49,s74,s122,s127,s135],[s5,s15,s21,s40,s74,s98,s113,s122,s127],[s10,s26,s35,s49,s82,s98,s122,s127],[s15,s26,s35,s40,s49,s74,s98,s122,s127]]
def B8_12 : List (List Sig) := [[s1,s5,s15,s21,s40,s49,s98,s122,s127],[s5,s10,s15,s21,s35,s89,s122,s127,s135],[s5,s10,s20,s21,s35,s74,s113,s122,s127],[s5,s10,s21,s40,s49,s82,s98,s122,s127],[s5,s10,s35,s55,s82,s98,s122,s127],[s5,s15,s21,s35,s40,s49,s74,s98,s130],[s5,s15,s21,s40,s49,s74,s109,s122,s127],[s10,s15,s21,s35,s49,s78,s102,s122,s127],[s10,s15,s26,s35,s49,s89,s98,s122,s127],[s10,s15,s26,s35,s74,s89,s98,s122,s127],[s15,s21,s35,s49,s78,s98,s102,s122,s127]]
def B8_13 : List (List Sig) := [[s5,s10,s15,s21,s35,s49,s89,s98,s130],[s5,s10,s15,s21,s35,s89,s109,s122,s127],[s5,s10,s15,s21,s35,s91,s98,s122,s127],[s5,s10,s15,s21,s59,s78,s98,s122,s127],[s5,s10,s15,s35,s55,s89,s98,s122,s127],[s5,s10,s21,s35,s54,s82,s98,s122,s127],[s5,s10,s21,s35,s63,s98,s122,s125,s127],[s5,s10,s21,s45,s49,s78,s98,s122,s127],[s5,s10,s21,s59,s63,s74,s98,s122,s127],[s5,s10,s31,s35,s74,s113,s122,s127],[s5,s15,s21,s35,s49,s78,s102,s122,s127],[s5,s21,s35,s49,s63,s74,s102,s122,s127],[s10,s15,s21,s35,s49,s86,s98,s122,s127],[s10,s15,s26,s35,s49,s85,s98,s122,s127],[s10,s26,s35,s49,s74,s98,s106,s122,s127]]
def B8_14 : List (List Sig) := [[s0,s5,s10,s21,s35,s49,s82,s122,s127],[s3,s5,s10,s21,s35,s74,s106,s122,s127],[s5,s10,s15,s21,s35,s49,s74,s106,s130],[s5,s10,s15,s21,s35,s49,s85,s98,s130],[s5,s10,s15,s21,s35,s50,s74,s122,s127],[s5,s10,s15,s21,s35,s59,s98,s122,s133],[s5,s10,s15,s21,s35,s113,s122,s127,s133],[s5,s10,s15,s35,s55,s74,s106,s122,s127],[s5,s10,s15,s35,s55,s85,s98,s122,s127],[s5,s10,s15,s35,s55,s92,s98,s122,s127],[s5,s10,s16,s21,s35,s49,s74,s122,s127],[s5,s10,s21,s35,s45,s49,s98,s122,s133],[s5,s10,s21,s35,s49,s82,s122,s135],[s5,s10,s21,s35,s49,s84,s98,s122,s127],[s5,s10,s21,s35,s72,s74,s98,s122,s127],[s5,s10,s26,s35,s49,s74,s106,s122,s127],[s5,s10,s35,s55,s74,s98,s106,s122,s127],[s5,s11,s15,s21,s35,s49,s74,s122,s127],[s5,s12,s21,s35,s49,s74,s98,s122,s127],[s5,s15,s21,s35,s40,s49,s74,s122,s135],[s5,s15,s21,s35,s49,s74,s102,s122,s133],[s10,s15,s21,s26,s35,s49,s74,s98,s130],[s10,s15,s26,s35,s49,s86,s98,s122,s127],[s10,s15,s26,s35,s55,s74,s98,s122,s127]]
def B8_15 : List (List Sig) := [[s5,s10,s15,s21,s35,s49,s89,s122,s135],[s5,s10,s15,s21,s35,s55,s74,s98,s130],[s5,s10,s15,s21,s35,s74,s89,s122,s135],[s5,s10,s31,s35,s49,s89,s98,s122,s127],[s5,s10,s31,s35,s74,s89,s98,s122,s127],[s5,s15,s21,s40,s62,s74,s98,s122,s127],[s10,s15,s21,s35,s78,s98,s113,s122,s127],[s15,s21,s40,s49,s78,s98,s122,s127]]
def B8_16 : List (List Sig) := [[s2,s10,s26,s35,s49,s74,s98,s122,s127],[s5,s10,s15,s21,s35,s49,s85,s122,s135],[s5,s10,s15,s21,s35,s74,s118,s122,s127],[s5,s10,s15,s21,s35,s78,s113,s122,s127],[s5,s10,s15,s21,s59,s98,s122,s125,s127],[s5,s10,s21,s35,s49,s74,s106,s122,s135],[s5,s10,s21,s35,s63,s74,s113,s122,s127],[s5,s10,s21,s35,s66,s74,s98,s122,s127],[s5,s10,s21,s35,s74,s98,s118,s122,s127],[s5,s10,s21,s35,s74,s113,s118,s122,s127],[s5,s10,s21,s45,s49,s98,s122,s125,s127],[s5,s10,s21,s45,s59,s74,s98,s122,s127],[s5,s10,s21,s70,s74,s98,s122,s127],[s5,s10,s31,s35,s49,s74,s106,s122,s127],[s5,s10,s31,s35,s49,s85,s98,s122,s127],[s5,s15,s21,s35,s49,s102,s122,s125,s127],[s5,s15,s21,s35,s59,s74,s102,s122,s127],[s5,s15,s21,s49,s59,s74,s102,s122,s127],[s5,s21,s35,s45,s49,s74,s102,s122,s127],[s10,s15,s21,s26,s35,s49,s74,s122,s135],[s10,s15,s21,s35,s49,s78,s109,s122,s127],[s10,s15,s26,s35,s63,s74,s98,s122,s127],[s10,s15,s35,s49,s55,s78,s98,s122,s127],[s10,s15,s35,s55,s74,s78,s98,s122,s127],[s10,s26,s31,s35,s49,s74,s98,s122,s127],[s10,s26,s34,s35,s49,s74,s98,s122,s127]]
def B8_17 : List (List Sig) := [[s2,s5,s10,s21,s35,s49,s74,s98,s130],[s2,s5,s10,s35,s55,s74,s98,s122,s127],[s5,s10,s15,s21,s35,s49,s113,s122,s133],[s5,s10,s15,s21,s35,s55,s74,s122,s135],[s5,s10,s15,s21,s35,s63,s74,s98,s130],[s5,s10,s15,s21,s35,s74,s113,s122,s133],[s5,s10,s21,s31,s35,s49,s74,s98,s130],[s5,s10,s26,s35,s63,s74,s98,s122,s127],[s5,s10,s31,s35,s55,s74,s98,s122,s127],[s5,s15,s21,s40,s53,s74,s98,s122,s127],[s5,s19,s21,s40,s49,s74,s98,s122,s127],[s10,s15,s26,s35,s49,s74,s98,s122,s130]]
def B8_18 : List (List Sig) := [[s3,s5,s10,s15,s21,s35,s98,s122,s133],[s5,s10,s15,s21,s35,s49,s74,s123,s127],[s5,s10,s15,s35,s55,s74,s98,s122,s130],[s5,s10,s19,s21,s35,s89,s98,s122,s127],[s5,s10,s21,s35,s49,s82,s98,s122,s133],[s5,s10,s21,s35,s49,s94,s98,s122,s127],[s5,s10,s21,s35,s74,s94,s98,s122,s127],[s10,s31,s35,s49,s74,s78,s98,s122,s127]]
def B8_19 : List (List Sig) := [[s2,s5,s10,s21,s35,s49,s74,s122,s135],[s5,s10,s15,s21,s35,s49,s74,s130,s136],[s5,s10,s15,s21,s35,s63,s74,s122,s135],[s5,s10,s15,s21,s35,s74,s100,s122,s127],[s5,s10,s15,s21,s35,s113,s122,s125,s127],[s5,s10,s15,s21,s59,s74,s113,s122,s127],[s5,s10,s18,s21,s35,s74,s98,s122,s127],[s5,s10,s21,s31,s35,s49,s74,s122,s135],[s5,s10,s21,s35,s45,s74,s113,s122,s127],[s5,s10,s21,s35,s49,s75,s98,s122,s127],[s5,s10,s21,s35,s49,s106,s122,s133],[s5,s10,s21,s35,s63,s74,s98,s122,s135],[s5,s10,s21,s37,s49,s74,s98,s122,s127],[s5,s10,s21,s45,s49,s74,s113,s122,s127],[s5,s10,s31,s35,s63,s74,s98,s122,s127],[s5,s10,s31,s35,s66,s74,s98,s122,s127],[s10,s15,s26,s35,s49,s74,s102,s122,s127],[s15,s26,s35,s49,s74,s98,s102,s122,s127]]
def B8_20 : List (List Sig) := [[s3,s5,s10,s21,s45,s74,s98,s122,s127],[s3,s5,s15,s21,s35,s74,s102,s122,s127],[s5,s10,s15,s21,s35,s49,s74,s102,s130],[s5,s10,s15,s21,s35,s49,s98,s130,s134],[s5,s10,s15,s21,s45,s49,s74,s98,s130],[s5,s10,s15,s26,s59,s74,s98,s122,s127],[s5,s10,s15,s35,s55,s74,s102,s122,s127],[s5,s10,s15,s45,s55,s74,s98,s122,s127],[s5,s10,s21,s35,s59,s82,s98,s122,s127],[s5,s10,s21,s49,s59,s82,s98,s122,s127],[s5,s10,s21,s59,s74,s82,s98,s122,s127],[s5,s10,s26,s45,s49,s74,s98,s122,s127],[s5,s10,s31,s35,s49,s74,s98,s122,s130],[s5,s15,s26,s35,s49,s74,s102,s122,s127],[s5,s21,s35,s49,s74,s82,s102,s122,s127],[s10,s15,s26,s35,s49,s74,s98,s127,s130]]
def B8_21 : List (List Sig) := [[s5,s10,s15,s35,s55,s74,s98,s127,s130],[s5,s10,s21,s59,s74,s106,s122,s127],[s10,s15,s21,s35,s53,s78,s98,s122,s127],[s10,s19,s21,s35,s49,s78,s98,s122,s127]]
def B8_22 : List (List Sig) := [[s5,s10,s15,s31,s59,s74,s98,s122,s127],[s5,s10,s21,s35,s49,s87,s98,s122,s127],[s5,s10,s21,s35,s63,s74,s122,s126,s127],[s5,s10,s21,s35,s63,s98,s122,s133],[s5,s10,s21,s63,s70,s74,s98,s122,s127],[s5,s10,s31,s35,s49,s74,s102,s122,s127],[s5,s10,s31,s45,s49,s74,s98,s122,s127],[s5,s15,s21,s35,s49,s74,s102,s122,s135],[s10,s15,s26,s35,s49,s74,s122,s127,s135],[s10,s15,s26,s35,s74,s98,s113,s122,s127],[s15,s26,s40,s49,s74,s98,s122,s127]]
def B8_23 : List (List Sig) := [[s1,s10,s15,s26,s35,s49,s98,s122,s127],[s5,s10,s15,s21,s35,s49,s74,s130,s135],[s5,s10,s15,s21,s35,s49,s122,s126,s133],[s5,s10,s15,s26,s35,s74,s113,s122,s127],[s5,s10,s15,s35,s55,s74,s122,s127,s135],[s5,s10,s21,s35,s49,s82,s113,s122,s127],[s5,s10,s21,s35,s74,s82,s113,s122,s127],[s5,s10,s31,s35,s49,s74,s98,s127,s130],[s5,s15,s21,s40,s49,s74,s98,s130],[s10,s15,s26,s35,s49,s74,s109,s122,s127],[s10,s15,s26,s35,s49,s82,s98,s122,s127],[s10,s15,s26,s35,s89,s98,s122,s127]]
def B8_24 : List (List Sig) := [[s1,s5,s10,s15,s21,s35,s49,s98,s130],[s1,s5,s10,s15,s35,s55,s98,s122,s127],[s3,s5,s10,s21,s35,s82,s98,s122,s127],[s5,s10,s15,s21,s35,s49,s74,s109,s130],[s5,s10,s15,s21,s35,s49,s82,s98,s130],[s5,s10,s15,s21,s40,s89,s98,s122,s127],[s5,s10,s15,s35,s49,s55,s74,s98,s130],[s5,s10,s15,s35,s55,s74,s109,s122,s127],[s5,s10,s15,s35,s55,s82,s98,s122,s127],[s5,s10,s26,s35,s49,s82,s98,s122,s127],[s5,s15,s21,s40,s54,s74,s98,s122,s127],[s5,s20,s21,s40,s49,s74,s98,s122,s127],[s5,s21,s35,s63,s74,s102,s122,s127]]
def B8_25 : List (List Sig) := [[s0,s5,s15,s21,s40,s49,s74,s122,s127],[s5,s10,s15,s21,s35,s74,s113,s122,s135],[s5,s10,s15,s21,s59,s74,s122,s126,s127],[s5,s10,s15,s31,s35,s74,s113,s122,s127],[s5,s10,s20,s21,s35,s89,s98,s122,s127],[s5,s10,s21,s45,s49,s74,s122,s126,s127],[s5,s10,s21,s45,s70,s74,s98,s122,s127],[s5,s10,s31,s35,s49,s74,s122,s127,s135],[s5,s10,s31,s35,s49,s87,s98,s122,s127],[s5,s10,s31,s35,s74,s98,s113,s122,s127],[s5,s10,s35,s49,s66,s74,s98,s122,s127],[s5,s15,s21,s35,s74,s102,s115,s122,s127],[s5,s20,s21,s35,s54,s74,s98,s122,s127],[s5,s21,s35,s40,s49,s74,s106,s122,s127]]
def B8_26 : List (List Sig) := [[s0,s5,s10,s15,s21,s35,s89,s122,s127],[s1,s5,s10,s15,s21,s35,s49,s122,s135],[s1,s5,s10,s31,s35,s49,s98,s122,s127],[s5,s10,s15,s21,s35,s49,s82,s122,s135],[s5,s10,s15,s21,s35,s89,s122,s135],[s5,s10,s21,s35,s49,s82,s98,s122,s135],[s5,s10,s21,s35,s49,s89,s106,s122,s127],[s5,s10,s21,s35,s74,s89,s106,s122,s127],[s5,s10,s31,s35,s49,s74,s109,s122,s127],[s5,s10,s31,s35,s49,s82,s98,s122,s127],[s5,s10,s31,s35,s89,s98,s122,s127],[s5,s15,s21,s40,s49,s98,s122,s127,s133]]
def B8_27 : List (List Sig) := [[s5,s10,s15,s22,s35,s49,s98,s122,s127],[s5,s10,s21,s35,s49,s85,s106,s122,s127],[s5,s15,s21,s59,s74,s102,s122,s127],[s5,s21,s45,s49,s74,s102,s122,s127],[s10,s15,s21,s40,s49,s78,s98,s122,s127],[s10,s15,s35,s55,s78,s98,s122,s127]]
def B8_28 : List (List Sig) := [[s5,s10,s15,s21,s35,s113,s122,s133],[s5,s10,s15,s21,s70,s74,s98,s122,s127],[s5,s10,s15,s35,s58,s74,s98,s122,s127],[s5,s10,s21,s35,s55,s74,s106,s122,s127],[s5,s15,s21,s40,s49,s74,s110,s122,s127],[s5,s15,s21,s40,s49,s78,s98,s122,s127],[s5,s21,s35,s40,s63,s74,s98,s122,s127],[s5,s21,s40,s49,s63,s74,s98,s122,s127],[s10,s15,s21,s35,s54,s78,s98,s122,s127],[s10,s15,s26,s35,s53,s74,s98,s122,s127],[s10,s19,s26,s35,s49,s74,s98,s122,s127],[s10,s20,s21,s35,s49,s78,s98,s122,s127]]
def B8_29 : List (List Sig) := [[s0,s10,s15,s21,s35,s49,s78,s122,s127],[s5,s10,s15,s21,s35,s49,s98,s124,s127],[s5,s10,s15,s21,s35,s53,s74,s98,s130],[s5,s10,s19,s21,s35,s49,s74,s98,s130],[s5,s10,s19,s35,s55,s74,s98,s122,s127],[s5,s10,s21,s35,s49,s82,s122,s126,s127],[s5,s10,s21,s35,s63,s89,s98,s122,s127],[s5,s10,s21,s35,s94,s98,s122,s127],[s5,s15,s21,s35,s40,s49,s98,s122,s133],[s5,s15,s21,s40,s49,s74,s98,s122,s133],[s10,s15,s21,s35,s78,s91,s98,s122,s127],[s10,s31,s35,s49,s78,s98,s122,s127]]
def B8_30 : List (List Sig) := [[s5,s10,s15,s21,s35,s89,s98,s122,s133],[s5,s10,s21,s35,s63,s74,s106,s122,s127],[s5,s10,s21,s35,s63,s85,s98,s122,s127],[s5,s10,s21,s35,s74,s106,s118,s122,s127],[s5,s10,s21,s45,s74,s113,s122,s127],[s10,s21,s26,s35,s63,s74,s98,s122,s127],[s10,s21,s35,s49,s78,s84,s98,s122,s127]]
def B8_31 : List (List Sig) := [[s5,s10,s15,s21,s35,s49,s106,s122,s133],[s5,s10,s15,s21,s35,s49,s125,s126,s127],[s5,s10,s15,s21,s35,s53,s74,s122,s135],[s5,s10,s19,s21,s35,s49,s74,s122,s135],[s5,s10,s21,s35,s49,s74,s106,s122,s130],[s5,s10,s21,s35,s49,s98,s106,s122,s133],[s5,s10,s21,s35,s89,s94,s98,s122,s127],[s5,s10,s21,s45,s49,s74,s111,s122,s127],[s5,s10,s21,s59,s82,s98,s122,s127],[s5,s10,s31,s35,s53,s74,s98,s122,s127],[s5,s15,s21,s40,s49,s98,s122,s125,s127],[s5,s15,s21,s40,s59,s74,s98,s122,s127],[s5,s21,s40,s45,s49,s74,s98,s122,s127],[s10,s15,s21,s26,s35,s49,s98,s122,s133]]
def B8_32 : List (List Sig) := [[s5,s10,s15,s21,s35,s55,s98,s122,s133],[s5,s10,s15,s21,s59,s89,s98,s122,s127],[s5,s10,s21,s35,s45,s89,s98,s122,s127],[s5,s10,s21,s45,s49,s89,s98,s122,s127],[s5,s10,s21,s45,s74,s89,s98,s122,s127],[s5,s15,s21,s35,s74,s89,s102,s122,s127],[s8,s10,s15,s21,s35,s74,s98,s122,s127],[s10,s21,s35,s49,s63,s78,s98,s122,s127],[s10,s21,s35,s63,s74,s78,s98,s122,s127]]
def B8_33 : List (List Sig) := [[s5,s10,s15,s21,s59,s74,s106,s122,s127],[s5,s10,s15,s21,s59,s85,s98,s122,s127],[s5,s10,s21,s45,s49,s74,s106,s122,s127],[s5,s10,s21,s45,s49,s85,s98,s122,s127],[s5,s10,s21,s59,s74,s98,s106,s122,s127],[s5,s15,s21,s35,s49,s85,s102,s122,s127],[s5,s21,s35,s49,s74,s102,s106,s122,s127],[s10,s15,s21,s35,s49,s78,s98,s122,s133],[s15,s21,s26,s35,s49,s74,s102,s122,s127]]
def B8_34 : List (List Sig) := [[s2,s5,s10,s21,s35,s49,s98,s122,s133],[s5,s10,s15,s21,s35,s63,s98,s122,s133],[s5,s10,s21,s31,s35,s49,s98,s122,s133],[s5,s10,s21,s35,s49,s74,s108,s122,s127],[s5,s10,s21,s35,s63,s74,s98,s122,s130],[s5,s10,s21,s35,s82,s113,s122,s127],[s5,s10,s21,s45,s55,s74,s98,s122,s127],[s5,s15,s21,s35,s40,s74,s113,s122,s127],[s5,s15,s21,s35,s55,s74,s102,s122,s127],[s5,s15,s21,s40,s49,s74,s113,s122,s127],[s7,s10,s21,s35,s49,s74,s98,s122,s127],[s10,s15,s26,s35,s49,s74,s98,s130],[s10,s15,s26,s40,s49,s74,s98,s122,s127]]
def B8_35 : List (List Sig) := [[s3,s5,s15,s21,s40,s74,s98,s122,s127],[s5,s10,s15,s21,s35,s89,s113,s122,s127],[s5,s10,s15,s21,s40,s49,s74,s98,s130],[s5,s10,s15,s35,s55,s74,s98,s130],[s5,s10,s15,s40,s55,s74,s98,s122,s127],[s5,s10,s21,s35,s63,s94,s98,s122,s127],[s5,s10,s21,s35,s68,s74,s98,s122,s127],[s5,s15,s26,s40,s49,s74,s98,s122,s127],[s5,s21,s40,s49,s74,s82,s98,s122,s127],[s10,s15,s21,s35,s59,s78,s98,s122,s127],[s10,s15,s26,s35,s54,s74,s98,s122,s127],[s10,s20,s26,s35,s49,s74,s98,s122,s127],[s10,s21,s35,s45,s49,s78,s98,s122,s127],[s15,s21,s35,s49,s74,s78,s102,s122,s127]]
def B8_36 : List (List Sig) := [[s0,s10,s15,s26,s35,s49,s74,s122,s127],[s2,s5,s10,s21,s59,s74,s98,s122,s127],[s2,s5,s21,s35,s49,s74,s102,s122,s127],[s5,s10,s15,s21,s35,s54,s74,s98,s130],[s5,s10,s15,s21,s35,s85,s113,s122,s127],[s5,s10,s15,s21,s35,s92,s98,s122,s127],[s5,s10,s15,s26,s35,s89,s98,s122,s127],[s5,s10,s20,s21,s35,s49,s74,s98,s130],[s5,s10,s20,s35,s55,s74,s98,s122,s127],[s5,s10,s21,s31,s59,s74,s98,s122,s127],[s5,s10,s21,s35,s63,s74,s102,s122,s127],[s5,s10,s21,s35,s74,s106,s113,s122,s127],[s5,s10,s21,s35,s82,s89,s98,s122,s127],[s5,s10,s21,s45,s63,s74,s98,s122,s127],[s5,s10,s35,s66,s74,s98,s122,s127],[s5,s15,s21,s35,s63,s74,s102,s122,s127],[s5,s21,s31,s35,s49,s74,s102,s122,s127],[s5,s21,s35,s63,s74,s98,s102,s122,s127],[s5,s21,s40,s49,s74,s106,s122,s127],[s10,s15,s26,s35,s49,s74,s122,s135]]
def B8_37 : List (List Sig) := [[s0,s5,s10,s15,s21,s35,s49,s74,s130],[s0,s5,s10,s15,s35,s55,s74,s122,s127],[s1,s5,s10,s21,s35,s49,s106,s122,s127],[s5,s10,s15,s21,s35,s49,s102,s122,s133],[s5,s10,s15,s21,s35,s76,s98,s122,s127],[s5,s10,s15,s21,s38,s74,s98,s122,s127],[s5,s10,s15,s21,s59,s74,s98,s122,s130],[s5,s10,s21,s35,s49,s82,s106,s122,s127],[s5,s10,s21,s35,s63,s74,s98,s127,s130],[s5,s10,s21,s35,s89,s106,s122,s127],[s5,s10,s21,s45,s49,s74,s98,s122,s130],[s5,s10,s31,s35,s49,s74,s98,s130],[s5,s10,s31,s40,s49,s74,s98,s122,s127],[s5,s10,s35,s49,s55,s74,s106,s122,s127],[s5,s15,s21,s35,s49,s74,s102,s122,s130],[s10,s15,s26,s35,s49,s98,s122,s127,s133],[s10,s21,s26,s35,s49,s82,s98,s122,s127]]
def B8_38 : List (List Sig) := [[s5,s10,s15,s21,s35,s49,s98,s130,s133],[s5,s10,s15,s21,s35,s54,s74,s122,s135],[s5,s10,s15,s21,s35,s89,s98,s122,s135],[s5,s10,s15,s31,s35,s89,s98,s122,s127],[s5,s10,s15,s35,s55,s98,s122,s127,s133],[s5,s10,s20,s21,s35,s49,s74,s122,s135],[s5,s10,s21,s35,s55,s82,s98,s122,s127],[s5,s10,s31,s35,s54,s74,s98,s122,s127]]
def B8_39 : List (List Sig) := [[s0,s5,s10,s31,s35,s49,s74,s122,s127],[s2,s5,s10,s21,s35,s74,s113,s122,s127],[s3,s10,s15,s21,s35,s78,s98,s122,s127],[s5,s10,s15,s21,s59,s74,s102,s122,s127],[s5,s10,s21,s31,s35,s74,s113,s122,s127],[s5,s10,s21,s35,s49,s74,s118,s122,s127],[s5,s10,s21,s35,s63,s74,s122,s127,s135],[s5,s10,s21,s45,s49,s74,s102,s122,s127],[s5,s15,s21,s35,s49,s74,s110,s122,s127],[s5,s15,s21,s45,s49,s74,s102,s122,s127],[s5,s15,s21,s59,s74,s98,s102,s122,s127],[s5,s21,s40,s63,s74,s98,s122,s127],[s5,s21,s45,s49,s74,s98,s102,s122,s127],[s10,s15,s26,s35,s49,s78,s98,s122,s127],[s10,s21,s35,s49,s78,s82,s98,s122,s127],[s10,s26,s35,s49,s63,s74,s98,s122,s127]]
def B8_40 : List (List Sig) := [[s1,s5,s10,s21,s35,s63,s98,s122,s127],[s5,s10,s15,s21,s35,s49,s78,s98,s130],[s5,s10,s15,s21,s35,s49,s122,s133,s135],[s5,s10,s15,s21,s35,s74,s113,s122,s130],[s5,s10,s15,s21,s35,s98,s113,s122,s133],[s5,s10,s15,s21,s59,s74,s98,s127,s130],[s5,s10,s15,s35,s55,s78,s98,s122,s127],[s5,s10,s21,s35,s49,s63,s74,s98,s130],[s5,s10,s21,s35,s63,s74,s109,s122,s127],[s5,s10,s21,s35,s63,s82,s98,s122,s127],[s5,s10,s21,s45,s49,s74,s98,s127,s130],[s5,s10,s31,s35,s49,s98,s122,s127,s133],[s5,s10,s35,s55,s63,s74,s98,s122,s127],[s5,s10,s35,s55,s66,s74,s98,s122,s127],[s5,s15,s21,s40,s49,s74,s122,s126,s127],[s5,s15,s21,s40,s49,s98,s122,s133]]
def B8_41 : List (List Sig) := [[s5,s10,s15,s21,s35,s49,s109,s122,s133],[s5,s10,s15,s21,s35,s89,s122,s126,s127],[s5,s10,s15,s21,s35,s94,s98,s122,s127],[s5,s10,s21,s35,s49,s82,s98,s122,s130],[s5,s10,s21,s48,s49,s74,s98,s122,s127],[s10,s15,s21,s35,s49,s78,s98,s122,s135],[s10,s15,s31,s35,s49,s78,s98,s122,s127]]
def B8_42 : List (List Sig) := [[s5,s10,s15,s21,s35,s49,s78,s122,s135],[s5,s10,s15,s21,s35,s51,s98,s122,s127],[s5,s10,s15,s21,s45,s74,s113,s122,s127],[s5,s10,s15,s21,s59,s74,s122,s127,s135],[s5,s10,s17,s21,s35,s49,s98,s122,s127],[s5,s10,s21,s35,s49,s63,s74,s122,s135],[s5,s10,s21,s35,s53,s74,s106,s122,s127],[s5,s10,s21,s35,s82,s94,s98,s122,s127],[s5,s10,s21,s45,s49,s74,s122,s127,s135],[s5,s10,s21,s45,s74,s98,s113,s122,s127],[s5,s10,s31,s35,s49,s78,s98,s122,s127],[s5,s10,s35,s63,s66,s74,s98,s122,s127],[s5,s13,s15,s21,s35,s74,s98,s122,s127],[s5,s15,s21,s35,s74,s102,s113,s122,s127],[s10,s15,s26,s35,s49,s98,s122,s125,s127],[s10,s15,s26,s35,s58,s74,s98,s122,s127],[s10,s15,s26,s35,s59,s74,s98,s122,s127],[s10,s26,s35,s45,s49,s74,s98,s122,s127]]
def B8_43 : List (List Sig) := [[s1,s5,s10,s15,s21,s59,s98,s122,s127],[s1,s5,s10,s21,s45,s49,s98,s122,s127],[s1,s5,s15,s21,s35,s49,s102,s122,s127],[s5,s10,s15,s21,s35,s49,s98,s125,s130],[s5,s10,s15,s21,s35,s59,s74,s98,s130],[s5,s10,s15,s21,s49,s59,s74,s98,s130],[s5,s10,s15,s21,s59,s74,s109,s122,s127],[s5,s10,s15,s21,s59,s82,s98,s122,s127],[s5,s10,s15,s35,s55,s98,s122,s125,s127],[s5,s10,s15,s55,s59,s74,s98,s122,s127],[s5,s10,s21,s35,s45,s49,s74,s98,s130],[s5,s10,s21,s35,s49,s82,s102,s122,s127],[s5,s10,s21,s45,s49,s74,s109,s122,s127],[s5,s10,s21,s45,s49,s82,s98,s122,s127],[s5,s10,s21,s45,s89,s98,s122,s127],[s5,s10,s35,s45,s55,s74,s98,s122,s127],[s5,s10,s45,s49,s55,s74,s98,s122,s127],[s10,s21,s35,s63,s78,s98,s122,s127]]
def B8_44 : List (List Sig) := [[s5,s10,s15,s21,s35,s49,s74,s122,s136],[s5,s10,s23,s35,s49,s74,s98,s122,s127],[s10,s15,s21,s35,s49,s78,s122,s126,s127]]
def B8_45 : List (List Sig) := [[s5,s10,s15,s21,s35,s49,s98,s122,s129],[s5,s10,s15,s21,s35,s49,s98,s122,s134],[s5,s10,s15,s21,s35,s49,s122,s125,s135],[s5,s10,s15,s21,s35,s59,s74,s122,s135],[s5,s10,s21,s35,s45,s49,s74,s122,s135],[s5,s10,s31,s35,s49,s98,s122,s125,s127],[s5,s10,s31,s35,s59,s74,s98,s122,s127],[s5,s10,s31,s49,s59,s74,s98,s122,s127],[s5,s15,s21,s40,s74,s113,s122,s127]]
def L8 : Level := [B8_0,B8_1,B8_2,B8_3,B8_4,B8_5,B8_6,B8_7,B8_8,B8_9,B8_10,B8_11,B8_12,B8_13,B8_14,B8_15,B8_16,B8_17,B8_18,B8_19,B8_20,B8_21,B8_22,B8_23,B8_24,B8_25,B8_26,B8_27,B8_28,B8_29,B8_30,B8_31,B8_32,B8_33,B8_34,B8_35,B8_36,B8_37,B8_38,B8_39,B8_40,B8_41,B8_42,B8_43,B8_44,B8_45]
def B9_0 : List (List Sig) := [[s5,s10,s15,s21,s35,s49,s78,s98,s122,s127],[s5,s10,s15,s21,s35,s49,s82,s98,s122,s127],[s5,s10,s15,s21,s40,s49,s74,s98,s122,s127],[s5,s10,s15,s21,s49,s59,s74,s98,s122,s127],[s5,s10,s19,s21,s35,s49,s74,s98,s122,s127],[s5,s10,s21,s35,s49,s74,s82,s98,s122,s127],[s10,s15,s21,s26,s35,s49,s74,s98,s122,s127],[s10,s15,s21,s35,s49,s74,s78,s98,s122,s127],[s10,s15,s26,s35,s49,s74,s98,s122,s127]]
def B9_1 : List (List Sig) := [[s5,s10,s15,s21,s35,s49,s74,s113,s122,s127],[s5,s10,s15,s21,s35,s49,s98,s122,s125,s127],[s5,s10,s15,s21,s59,s74,s98,s122,s127],[s5,s10,s15,s26,s35,s49,s74,s98,s122,s127],[s5,s10,s21,s35,s49,s63,s74,s98,s122,s127],[s5,s10,s21,s45,s49,s74,s98,s122,s127],[s5,s15,s21,s40,s49,s74,s98,s122,s127]]
def B9_2 : List (List Sig) := [[s1,s5,s10,s15,s21,s35,s49,s98,s122,s127],[s2,s5,s10,s21,s35,s49,s74,s98,s122,s127],[s3,s5,s10,s15,s21,s35,s74,s98,s122,s127],[s5,s10,s15,s21,s35,s49,s74,s98,s127,s130],[s5,s10,s15,s21,s35,s49,s74,s102,s122,s127],[s5,s10,s15,s21,s35,s49,s74,s109,s122,s127],[s5,s10,s15,s21,s35,s49,s74,s122,s126,s127],[s5,s10,s15,s21,s35,s49,s74,s122,s127,s135],[s5,s10,s15,s21,s35,s49,s85,s98,s122,s127],[s5,s10,s15,s21,s35,s49,s89,s98,s122,s127],[s5,s10,s15,s21,s35,s49,s98,s122,s127,s133],[s5,s10,s15,s21,s35,s59,s74,s98,s122,s127],[s5,s10,s15,s21,s35,s74,s98,s113,s122,s127],[s5,s10,s15,s21,s35,s74,s113,s122,s127],[s5,s10,s15,s21,s45,s49,s74,s98,s122,s127],[s5,s10,s15,s35,s49,s55,s74,s98,s122,s127],[s5,s10,s20,s21,s35,s49,s74,s98,s122,s127],[s5,s10,s21,s31,s35,s49,s74,s98,s122,s127],[s5,s10,s21,s35,s45,s49,s74,s98,s122,s127],[s5,s10,s21,s35,s49,s74,s98,s106,s122,s127],[s5,s10,s21,s35,s49,s74,s106,s122,s127],[s5,s10,s21,s35,s63,s74,s98,s122,s127],[s5,s10,s31,s35,s49,s74,s98,s122,s127],[s5,s15,s21,s35,s40,s49,s74,s98,s122,s127]]
def B9_3 : List (List Sig) := [[s0,s5,s10,s15,s21,s35,s49,s74,s122,s127],[s5,s10,s15,s21,s35,s49,s74,s98,s122,s135],[s5,s10,s15,s21,s35,s49,s74,s98,s130],[s5,s10,s15,s21,s35,s49,s74,s106,s122,s127],[s5,s10,s15,s21,s35,s49,s74,s122,s135],[s5,s10,s15,s21,s35,s49,s98,s122,s133],[s5,s10,s15,s21,s35,s55,s74,s98,s122,s127],[s5,s10,s15,s21,s35,s63,s74,s98,s122,s127],[s5,s10,s15,s21,s35,s89,s98,s122,s127],[s5,s10,s15,s31,s35,s49,s74,s98,s122,s127],[s5,s10,s15,s35,s55,s74,s98,s122,s127],[s5,s15,s21,s35,s49,s74,s98,s102,s122,s127],[s5,s15,s21,s35,s49,s74,s102,s122,s127]]
def B9_4 : List (List Sig) := [[s5,s10,s15,s21,s35,s49,s74,s98,s122,s130],[s5,s10,s15,s21,s35,s49,s74,s98,s122,s133],[s5,s10,s15,s21,s35,s53,s74,s98,s122,s127],[s5,s10,s15,s21,s35,s54,s74,s98,s122,s127],[s5,s10,s15,s21,s35,s74,s89,s98,s122,s127],[s5,s10,s21,s35,s49,s82,s98,s122,s127],[s10,s15,s21,s35,s49,s78,s98,s122,s127]]
def L9 : Level := [B9_0,B9_1,B9_2,B9_3,B9_4]
def B10_0 : List (List Sig) := [[s5,s10,s15,s21,s35,s49,s74,s98,s122,s127]]
def L10 : Level := [B10_0]
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v3 : Valid 3 L3 := by simp [Valid,L3]
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p4_0 : allParents 4 L3 B4_0=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v4 : Valid 4 L4 := by
  apply step v3
  intro b hb
  simp only [L4,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl
  · exact p4_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p5_0 : allParents 5 L4 B5_0=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p5_1 : allParents 5 L4 B5_1=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p5_2 : allParents 5 L4 B5_2=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p5_3 : allParents 5 L4 B5_3=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p5_4 : allParents 5 L4 B5_4=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p5_5 : allParents 5 L4 B5_5=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p5_6 : allParents 5 L4 B5_6=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p5_7 : allParents 5 L4 B5_7=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p5_8 : allParents 5 L4 B5_8=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p5_9 : allParents 5 L4 B5_9=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p5_10 : allParents 5 L4 B5_10=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p5_11 : allParents 5 L4 B5_11=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p5_12 : allParents 5 L4 B5_12=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p5_13 : allParents 5 L4 B5_13=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p5_14 : allParents 5 L4 B5_14=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p5_15 : allParents 5 L4 B5_15=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p5_16 : allParents 5 L4 B5_16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v5 : Valid 5 L5 := by
  apply step v4
  intro b hb
  simp only [L5,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact p5_0
  · exact p5_1
  · exact p5_2
  · exact p5_3
  · exact p5_4
  · exact p5_5
  · exact p5_6
  · exact p5_7
  · exact p5_8
  · exact p5_9
  · exact p5_10
  · exact p5_11
  · exact p5_12
  · exact p5_13
  · exact p5_14
  · exact p5_15
  · exact p5_16
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_0 : allParents 6 L5 B6_0=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_1 : allParents 6 L5 B6_1=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_2 : allParents 6 L5 B6_2=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_3 : allParents 6 L5 B6_3=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_4 : allParents 6 L5 B6_4=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_5 : allParents 6 L5 B6_5=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_6 : allParents 6 L5 B6_6=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_7 : allParents 6 L5 B6_7=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_8 : allParents 6 L5 B6_8=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_9 : allParents 6 L5 B6_9=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_10 : allParents 6 L5 B6_10=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_11 : allParents 6 L5 B6_11=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_12 : allParents 6 L5 B6_12=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_13 : allParents 6 L5 B6_13=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_14 : allParents 6 L5 B6_14=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_15 : allParents 6 L5 B6_15=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_16 : allParents 6 L5 B6_16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_17 : allParents 6 L5 B6_17=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_18 : allParents 6 L5 B6_18=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_19 : allParents 6 L5 B6_19=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_20 : allParents 6 L5 B6_20=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_21 : allParents 6 L5 B6_21=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_22 : allParents 6 L5 B6_22=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_23 : allParents 6 L5 B6_23=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_24 : allParents 6 L5 B6_24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_25 : allParents 6 L5 B6_25=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_26 : allParents 6 L5 B6_26=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_27 : allParents 6 L5 B6_27=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_28 : allParents 6 L5 B6_28=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_29 : allParents 6 L5 B6_29=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_30 : allParents 6 L5 B6_30=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_31 : allParents 6 L5 B6_31=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_32 : allParents 6 L5 B6_32=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_33 : allParents 6 L5 B6_33=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_34 : allParents 6 L5 B6_34=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_35 : allParents 6 L5 B6_35=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_36 : allParents 6 L5 B6_36=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_37 : allParents 6 L5 B6_37=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_38 : allParents 6 L5 B6_38=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_39 : allParents 6 L5 B6_39=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_40 : allParents 6 L5 B6_40=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_41 : allParents 6 L5 B6_41=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_42 : allParents 6 L5 B6_42=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_43 : allParents 6 L5 B6_43=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_44 : allParents 6 L5 B6_44=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_45 : allParents 6 L5 B6_45=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_46 : allParents 6 L5 B6_46=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_47 : allParents 6 L5 B6_47=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_48 : allParents 6 L5 B6_48=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_49 : allParents 6 L5 B6_49=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_50 : allParents 6 L5 B6_50=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_51 : allParents 6 L5 B6_51=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_52 : allParents 6 L5 B6_52=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_53 : allParents 6 L5 B6_53=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_54 : allParents 6 L5 B6_54=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_55 : allParents 6 L5 B6_55=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_56 : allParents 6 L5 B6_56=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_57 : allParents 6 L5 B6_57=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_58 : allParents 6 L5 B6_58=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_59 : allParents 6 L5 B6_59=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_60 : allParents 6 L5 B6_60=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_61 : allParents 6 L5 B6_61=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_62 : allParents 6 L5 B6_62=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_63 : allParents 6 L5 B6_63=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_64 : allParents 6 L5 B6_64=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_65 : allParents 6 L5 B6_65=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_66 : allParents 6 L5 B6_66=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_67 : allParents 6 L5 B6_67=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_68 : allParents 6 L5 B6_68=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_69 : allParents 6 L5 B6_69=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_70 : allParents 6 L5 B6_70=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_71 : allParents 6 L5 B6_71=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_72 : allParents 6 L5 B6_72=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_73 : allParents 6 L5 B6_73=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_74 : allParents 6 L5 B6_74=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_75 : allParents 6 L5 B6_75=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_76 : allParents 6 L5 B6_76=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_77 : allParents 6 L5 B6_77=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_78 : allParents 6 L5 B6_78=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_79 : allParents 6 L5 B6_79=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_80 : allParents 6 L5 B6_80=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_81 : allParents 6 L5 B6_81=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p6_82 : allParents 6 L5 B6_82=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v6 : Valid 6 L6 := by
  apply step v5
  intro b hb
  simp only [L6,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact p6_0
  · exact p6_1
  · exact p6_2
  · exact p6_3
  · exact p6_4
  · exact p6_5
  · exact p6_6
  · exact p6_7
  · exact p6_8
  · exact p6_9
  · exact p6_10
  · exact p6_11
  · exact p6_12
  · exact p6_13
  · exact p6_14
  · exact p6_15
  · exact p6_16
  · exact p6_17
  · exact p6_18
  · exact p6_19
  · exact p6_20
  · exact p6_21
  · exact p6_22
  · exact p6_23
  · exact p6_24
  · exact p6_25
  · exact p6_26
  · exact p6_27
  · exact p6_28
  · exact p6_29
  · exact p6_30
  · exact p6_31
  · exact p6_32
  · exact p6_33
  · exact p6_34
  · exact p6_35
  · exact p6_36
  · exact p6_37
  · exact p6_38
  · exact p6_39
  · exact p6_40
  · exact p6_41
  · exact p6_42
  · exact p6_43
  · exact p6_44
  · exact p6_45
  · exact p6_46
  · exact p6_47
  · exact p6_48
  · exact p6_49
  · exact p6_50
  · exact p6_51
  · exact p6_52
  · exact p6_53
  · exact p6_54
  · exact p6_55
  · exact p6_56
  · exact p6_57
  · exact p6_58
  · exact p6_59
  · exact p6_60
  · exact p6_61
  · exact p6_62
  · exact p6_63
  · exact p6_64
  · exact p6_65
  · exact p6_66
  · exact p6_67
  · exact p6_68
  · exact p6_69
  · exact p6_70
  · exact p6_71
  · exact p6_72
  · exact p6_73
  · exact p6_74
  · exact p6_75
  · exact p6_76
  · exact p6_77
  · exact p6_78
  · exact p6_79
  · exact p6_80
  · exact p6_81
  · exact p6_82
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_0 : allParents 7 L6 B7_0=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_1 : allParents 7 L6 B7_1=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_2 : allParents 7 L6 B7_2=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_3 : allParents 7 L6 B7_3=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_4 : allParents 7 L6 B7_4=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_5 : allParents 7 L6 B7_5=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_6 : allParents 7 L6 B7_6=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_7 : allParents 7 L6 B7_7=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_8 : allParents 7 L6 B7_8=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_9 : allParents 7 L6 B7_9=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_10 : allParents 7 L6 B7_10=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_11 : allParents 7 L6 B7_11=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_12 : allParents 7 L6 B7_12=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_13 : allParents 7 L6 B7_13=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_14 : allParents 7 L6 B7_14=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_15 : allParents 7 L6 B7_15=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_16 : allParents 7 L6 B7_16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_17 : allParents 7 L6 B7_17=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_18 : allParents 7 L6 B7_18=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_19 : allParents 7 L6 B7_19=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_20 : allParents 7 L6 B7_20=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_21 : allParents 7 L6 B7_21=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_22 : allParents 7 L6 B7_22=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_23 : allParents 7 L6 B7_23=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_24 : allParents 7 L6 B7_24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_25 : allParents 7 L6 B7_25=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_26 : allParents 7 L6 B7_26=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_27 : allParents 7 L6 B7_27=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_28 : allParents 7 L6 B7_28=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_29 : allParents 7 L6 B7_29=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_30 : allParents 7 L6 B7_30=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_31 : allParents 7 L6 B7_31=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_32 : allParents 7 L6 B7_32=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_33 : allParents 7 L6 B7_33=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_34 : allParents 7 L6 B7_34=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_35 : allParents 7 L6 B7_35=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_36 : allParents 7 L6 B7_36=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_37 : allParents 7 L6 B7_37=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_38 : allParents 7 L6 B7_38=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_39 : allParents 7 L6 B7_39=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_40 : allParents 7 L6 B7_40=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_41 : allParents 7 L6 B7_41=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_42 : allParents 7 L6 B7_42=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_43 : allParents 7 L6 B7_43=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_44 : allParents 7 L6 B7_44=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_45 : allParents 7 L6 B7_45=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_46 : allParents 7 L6 B7_46=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_47 : allParents 7 L6 B7_47=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_48 : allParents 7 L6 B7_48=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_49 : allParents 7 L6 B7_49=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_50 : allParents 7 L6 B7_50=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_51 : allParents 7 L6 B7_51=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_52 : allParents 7 L6 B7_52=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_53 : allParents 7 L6 B7_53=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_54 : allParents 7 L6 B7_54=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_55 : allParents 7 L6 B7_55=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_56 : allParents 7 L6 B7_56=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_57 : allParents 7 L6 B7_57=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_58 : allParents 7 L6 B7_58=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_59 : allParents 7 L6 B7_59=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_60 : allParents 7 L6 B7_60=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_61 : allParents 7 L6 B7_61=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_62 : allParents 7 L6 B7_62=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_63 : allParents 7 L6 B7_63=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_64 : allParents 7 L6 B7_64=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_65 : allParents 7 L6 B7_65=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_66 : allParents 7 L6 B7_66=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_67 : allParents 7 L6 B7_67=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_68 : allParents 7 L6 B7_68=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_69 : allParents 7 L6 B7_69=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_70 : allParents 7 L6 B7_70=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_71 : allParents 7 L6 B7_71=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_72 : allParents 7 L6 B7_72=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_73 : allParents 7 L6 B7_73=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_74 : allParents 7 L6 B7_74=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_75 : allParents 7 L6 B7_75=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_76 : allParents 7 L6 B7_76=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_77 : allParents 7 L6 B7_77=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_78 : allParents 7 L6 B7_78=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_79 : allParents 7 L6 B7_79=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_80 : allParents 7 L6 B7_80=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_81 : allParents 7 L6 B7_81=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_82 : allParents 7 L6 B7_82=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_83 : allParents 7 L6 B7_83=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_84 : allParents 7 L6 B7_84=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_85 : allParents 7 L6 B7_85=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_86 : allParents 7 L6 B7_86=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_87 : allParents 7 L6 B7_87=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_88 : allParents 7 L6 B7_88=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_89 : allParents 7 L6 B7_89=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_90 : allParents 7 L6 B7_90=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_91 : allParents 7 L6 B7_91=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_92 : allParents 7 L6 B7_92=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_93 : allParents 7 L6 B7_93=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_94 : allParents 7 L6 B7_94=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_95 : allParents 7 L6 B7_95=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_96 : allParents 7 L6 B7_96=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_97 : allParents 7 L6 B7_97=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_98 : allParents 7 L6 B7_98=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_99 : allParents 7 L6 B7_99=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_100 : allParents 7 L6 B7_100=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_101 : allParents 7 L6 B7_101=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_102 : allParents 7 L6 B7_102=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_103 : allParents 7 L6 B7_103=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_104 : allParents 7 L6 B7_104=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_105 : allParents 7 L6 B7_105=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_106 : allParents 7 L6 B7_106=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_107 : allParents 7 L6 B7_107=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_108 : allParents 7 L6 B7_108=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_109 : allParents 7 L6 B7_109=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_110 : allParents 7 L6 B7_110=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p7_111 : allParents 7 L6 B7_111=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v7 : Valid 7 L7 := by
  apply step v6
  intro b hb
  simp only [L7,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact p7_0
  · exact p7_1
  · exact p7_2
  · exact p7_3
  · exact p7_4
  · exact p7_5
  · exact p7_6
  · exact p7_7
  · exact p7_8
  · exact p7_9
  · exact p7_10
  · exact p7_11
  · exact p7_12
  · exact p7_13
  · exact p7_14
  · exact p7_15
  · exact p7_16
  · exact p7_17
  · exact p7_18
  · exact p7_19
  · exact p7_20
  · exact p7_21
  · exact p7_22
  · exact p7_23
  · exact p7_24
  · exact p7_25
  · exact p7_26
  · exact p7_27
  · exact p7_28
  · exact p7_29
  · exact p7_30
  · exact p7_31
  · exact p7_32
  · exact p7_33
  · exact p7_34
  · exact p7_35
  · exact p7_36
  · exact p7_37
  · exact p7_38
  · exact p7_39
  · exact p7_40
  · exact p7_41
  · exact p7_42
  · exact p7_43
  · exact p7_44
  · exact p7_45
  · exact p7_46
  · exact p7_47
  · exact p7_48
  · exact p7_49
  · exact p7_50
  · exact p7_51
  · exact p7_52
  · exact p7_53
  · exact p7_54
  · exact p7_55
  · exact p7_56
  · exact p7_57
  · exact p7_58
  · exact p7_59
  · exact p7_60
  · exact p7_61
  · exact p7_62
  · exact p7_63
  · exact p7_64
  · exact p7_65
  · exact p7_66
  · exact p7_67
  · exact p7_68
  · exact p7_69
  · exact p7_70
  · exact p7_71
  · exact p7_72
  · exact p7_73
  · exact p7_74
  · exact p7_75
  · exact p7_76
  · exact p7_77
  · exact p7_78
  · exact p7_79
  · exact p7_80
  · exact p7_81
  · exact p7_82
  · exact p7_83
  · exact p7_84
  · exact p7_85
  · exact p7_86
  · exact p7_87
  · exact p7_88
  · exact p7_89
  · exact p7_90
  · exact p7_91
  · exact p7_92
  · exact p7_93
  · exact p7_94
  · exact p7_95
  · exact p7_96
  · exact p7_97
  · exact p7_98
  · exact p7_99
  · exact p7_100
  · exact p7_101
  · exact p7_102
  · exact p7_103
  · exact p7_104
  · exact p7_105
  · exact p7_106
  · exact p7_107
  · exact p7_108
  · exact p7_109
  · exact p7_110
  · exact p7_111
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_0 : allParents 8 L7 B8_0=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_1 : allParents 8 L7 B8_1=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_2 : allParents 8 L7 B8_2=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_3 : allParents 8 L7 B8_3=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_4 : allParents 8 L7 B8_4=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_5 : allParents 8 L7 B8_5=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_6 : allParents 8 L7 B8_6=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_7 : allParents 8 L7 B8_7=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_8 : allParents 8 L7 B8_8=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_9 : allParents 8 L7 B8_9=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_10 : allParents 8 L7 B8_10=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_11 : allParents 8 L7 B8_11=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_12 : allParents 8 L7 B8_12=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_13 : allParents 8 L7 B8_13=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_14 : allParents 8 L7 B8_14=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_15 : allParents 8 L7 B8_15=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_16 : allParents 8 L7 B8_16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_17 : allParents 8 L7 B8_17=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_18 : allParents 8 L7 B8_18=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_19 : allParents 8 L7 B8_19=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_20 : allParents 8 L7 B8_20=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_21 : allParents 8 L7 B8_21=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_22 : allParents 8 L7 B8_22=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_23 : allParents 8 L7 B8_23=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_24 : allParents 8 L7 B8_24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_25 : allParents 8 L7 B8_25=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_26 : allParents 8 L7 B8_26=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_27 : allParents 8 L7 B8_27=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_28 : allParents 8 L7 B8_28=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_29 : allParents 8 L7 B8_29=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_30 : allParents 8 L7 B8_30=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_31 : allParents 8 L7 B8_31=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_32 : allParents 8 L7 B8_32=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_33 : allParents 8 L7 B8_33=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_34 : allParents 8 L7 B8_34=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_35 : allParents 8 L7 B8_35=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_36 : allParents 8 L7 B8_36=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_37 : allParents 8 L7 B8_37=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_38 : allParents 8 L7 B8_38=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_39 : allParents 8 L7 B8_39=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_40 : allParents 8 L7 B8_40=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_41 : allParents 8 L7 B8_41=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_42 : allParents 8 L7 B8_42=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_43 : allParents 8 L7 B8_43=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_44 : allParents 8 L7 B8_44=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p8_45 : allParents 8 L7 B8_45=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v8 : Valid 8 L8 := by
  apply step v7
  intro b hb
  simp only [L8,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact p8_0
  · exact p8_1
  · exact p8_2
  · exact p8_3
  · exact p8_4
  · exact p8_5
  · exact p8_6
  · exact p8_7
  · exact p8_8
  · exact p8_9
  · exact p8_10
  · exact p8_11
  · exact p8_12
  · exact p8_13
  · exact p8_14
  · exact p8_15
  · exact p8_16
  · exact p8_17
  · exact p8_18
  · exact p8_19
  · exact p8_20
  · exact p8_21
  · exact p8_22
  · exact p8_23
  · exact p8_24
  · exact p8_25
  · exact p8_26
  · exact p8_27
  · exact p8_28
  · exact p8_29
  · exact p8_30
  · exact p8_31
  · exact p8_32
  · exact p8_33
  · exact p8_34
  · exact p8_35
  · exact p8_36
  · exact p8_37
  · exact p8_38
  · exact p8_39
  · exact p8_40
  · exact p8_41
  · exact p8_42
  · exact p8_43
  · exact p8_44
  · exact p8_45
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p9_0 : allParents 9 L8 B9_0=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p9_1 : allParents 9 L8 B9_1=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p9_2 : allParents 9 L8 B9_2=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p9_3 : allParents 9 L8 B9_3=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p9_4 : allParents 9 L8 B9_4=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v9 : Valid 9 L9 := by
  apply step v8
  intro b hb
  simp only [L9,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact p9_0
  · exact p9_1
  · exact p9_2
  · exact p9_3
  · exact p9_4
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem p10_0 : allParents 10 L9 B10_0=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10 : Valid 10 L10 := by
  apply step v9
  intro b hb
  simp only [L10,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl
  · exact p10_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem certificate : ImpossibleM target 10 inputs.toFinset := by
  let ws := [s5,s10,s15,s21,s35,s49,s74,s98,s122,s127]
  have outer : B10_0 ∈ L10 := by simp [L10]
  have inner : ws ∈ B10_0 := by simp [ws,B10_0]
  have eq : inputs.toFinset=ws.toFinset := by dsimp only [ws]; decide
  rw [eq]
  exact v10 _ outer _ inner
end PEqualNP.Outside.L_meta_9399

theorem PEqualNP.Outside.L_meta_9399 :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3687098 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_9399.goal_of PEqualNP.Outside.L_meta_9399.certificate

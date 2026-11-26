import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9822.Ranked
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 1024
def zero : Sig := 0
def one : Sig := BitVec.allOnes 1024
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
def bit (i : Fin 1024) (a : Sig) : Bool := a.getLsbD i.val
theorem bit_zero (i) : bit i zero = false := by simp [bit,zero]
theorem bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
theorem bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
abbrev Row := Fin 1024
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

theorem kwWidth {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega
def onlyWire (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, bit p w=true → bit n w=false → w=v
def kwWireB (ws : List Sig) (T v : Sig) (p n : Row) : Bool :=
  bit p T && !bit n T && ws.all (fun w => !bit p w || bit n w || w==v)
theorem kwWireB_sound {ws T v p n} (h : kwWireB ws T v p n=true) :
    onlyWire ws.toFinset T v p n := by
  simp only [kwWireB,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw hp hn
  simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using
    h.2 w (List.mem_toFinset.mp hw)
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
def rows (v i : Nat) : Row := Fin.ofNat 1024 ((v >>> (10*i)) % 1024)
def excluded (ws : List Sig) (T a b : Sig) (t : Nat) : Bool :=
  (a != b) && kwWireB ws T a (rows t 0) (rows t 2) && kwWireB ws T b (rows t 0) (rows t 3) &&
    kwWireB ws T a (rows t 4) (rows t 1) && kwWireB ws T b (rows t 5) (rows t 1)
theorem different {ws T a b t f} (ok : excluded ws T a b t=true)
    (law : orderLaw ws.toFinset T f) : f a ≠ f b := by
  simp only [excluded,Bool.and_eq_true,bne_iff_ne] at ok
  exact law.1 ok.1.1.1.1 (kwWireB_sound ok.1.1.1.2) (kwWireB_sound ok.1.1.2)
    (kwWireB_sound ok.1.2) (kwWireB_sound ok.2)
def child (bank : List Sig) (d : Nat) :=
  let a := bank.getD (d%32) zero
  let b := bank.getD ((d>>>5)%32) zero
  if d>>>10=4 then neg a else bin (d>>>10) a b
def liveList (m : Nat) : List Sig → List Sig
  | [] => []
  | a::as => if m%2=1 then a::liveList (m/2) as else liveList (m/2) as
abbrev Sample := Nat × List Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat
def state (raw : List Sig) (s : Sample) :=
  liveList s.2.2.1 (s.2.1.foldl (fun bank d => bank++[child bank d]) raw)
def replay (raw : List Sig) (T : Sig) (s : Sample) :=
  let (k,_,_,c,i,j,l,x,y,z) := s
  let ws := state raw s
  let a := ws.getD i zero
  let b := ws.getD j zero
  let d := ws.getD l zero
  ((ws.contains a && ws.contains b) && excluded ws T a b x) &&
    (if c=2 then decide (k+1≤ws.toFinset.card) else
      decide (k≤ws.toFinset.card) && ws.contains d && excluded ws T a d y && excluded ws T b d z)
theorem replay_sound {raw T s} (ok : replay raw T s=true) :
    ∀ k, k ≤ s.1 → ¬Live false T k (state raw s).toFinset := by
  obtain ⟨cap,ops,m,c,i,j,l,x,y,z⟩ := s
  let ws := state raw (cap,ops,m,c,i,j,l,x,y,z)
  let a := ws.getD i zero
  let b := ws.getD j zero
  let d := ws.getD l zero
  change (((ws.contains a && ws.contains b) && excluded ws T a b x) &&
    (if c=2 then decide (cap+1≤ws.toFinset.card) else
      decide (cap≤ws.toFinset.card) && ws.contains d && excluded ws T a d y && excluded ws T b d z))=true at ok
  intro k hk run
  change Live false T k ws.toFinset at run
  change k ≤ cap at hk
  obtain ⟨count,f,size,bounds,law⟩ := order_live run
  simp only [Bool.and_eq_true,List.contains_eq_mem,decide_eq_true_eq] at ok
  have ha := bounds a (List.mem_toFinset.mpr ok.1.1.1)
  have hb := bounds b (List.mem_toFinset.mpr ok.1.1.2)
  have ab := different ok.1.2 law
  by_cases hc : c=2
  · have small : cap+1 ≤ ws.toFinset.card := by simpa [hc] using ok.2
    omega
  · have more := ok.2
    simp only [hc,if_false,Bool.and_eq_true,List.contains_eq_mem,decide_eq_true_eq] at more
    have hd := bounds d (List.mem_toFinset.mpr more.1.1.2)
    have ad := different more.1.2 law
    have bd := different more.2 law
    obtain ⟨⟨⟨sc,_⟩,_⟩,_⟩ := more
    omega

def raw : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
def target : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0ffffffffffffffffffffffffffffffffffffffffffffffffffffeaeaffffc0c0fffffffffffffffffffffffffffafff0ffffffffffffffffffffffffffeaffc0fffffffffffefcfcfffffffffffaf0f0ffeeeeeeffeeccccffeaeaeaffeac0c0
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S
theorem coordinate0 : ∀ r : Row, bit r (raw.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (raw.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (raw.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (raw.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (raw.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (raw.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (raw.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (raw.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (raw.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem coordinate9 : ∀ r : Row, bit r (raw.getD 9 zero) = r.val.testBit 9 := by decide +kernel
theorem input_coords : ∀ (j : Fin 10) (r : Row), bit r (raw.getD j.val zero) = r.val.testBit j.val := by
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
def colorPoint (v : Fin 10 → Bool) : Row :=
  (BitVec.ofBoolListLE (List.ofFn v)).toFin.cast (by simp [List.length_ofFn])
theorem color_bit (v : Fin 10 → Bool) (i : Fin 10) :
    bit (colorPoint v) (raw.getD i.val zero) = v i := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn v)).getLsbD i.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def colorField (d j : Nat) : Fin 10 := Fin.ofNat 10 ((d >>> (1+4*j)) % 16)
def colorRow (d j : Nat) : Row := Fin.ofNat 1024 ((d >>> (13+10*j)) % 1024)
def colorWire (ws : List Sig) (names : Nat) (j : Fin 10) : Sig :=
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
def rankRule (d : Nat) (f : Fin 10 → Nat) : Prop :=
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
def layerCovers (lo : Nat) (f : Fin 10 → Nat) (t : Nat) :=
  ∀ i, f i<t → lo.testBit i.val=true
def layerBits (lo : Nat) (f : Fin 10 → Nat) (t : Nat) (i : Fin 10) :=
  !lo.testBit i.val && decide (f i=t)
def layerRule (lo d : Nat) : Sig :=
  let x := fun j => raw.getD (colorField d j).val zero
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
def cubeParts (mask : Nat) : List (Fin 10) → Sig
  | [] => one
  | i::is => if mask.testBit i.val then cubeParts mask is else
      prime false (neg (raw.getD i.val zero)) (cubeParts mask is)
theorem cube_parts {x : Fin 10 → Bool} (mask : Nat) (is : List (Fin 10))
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
def cubeWord (mask : Nat) := cubeParts mask (List.finRange 10)
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
          exact cube_parts a (List.finRange 10) hit i (by simp) yes
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
    have top (i : Fin 10) (no : a.testBit i.val=false) : f i=t := by
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
    (List.finRange 10).all (fun i => decide (colorWire ws names i ∈ ws)) &&
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

abbrev OrderSample := Nat × List Nat × Nat × OrderPage
def orderState (s : OrderSample) := liveList s.2.2.1 (s.2.1.foldl (fun bank d => bank++[child bank d]) raw)
def verifyOrder (s : OrderSample) := orderCheck (orderState s) target s.1 s.2.2.2
def hornSamples : List OrderSample := [
(13,[1056,1186,1284,1155],16367,1464,[4870242294441365872679,4870536746837926739973,226553969736769732641,585052274697794,5070003380560390],0,[[1009,1010,1020]]),
(14,[1056,1186,1155],8191,5268617,[4870242294441365872713,5312882006816513458181,2951781186637322780715,2656927457992778448935,4870536746837926739975,585052274698340,2537784925628452,293724869502120,2818203566875688,5070003380560904,583996459328616,4650981782726730,587182580695658,4649115436976642],0,[[962,964,968,976,993],[982,988,995,1001,1002,1013]]),
(14,[1056,1088,1155],8190,157840692,[5312882006816513458307,304589882230617284803,1217787240521758146721,2951781186637322780769,159396295281951908033,2656927457992778448997,4870536746837926740101,4871385130009919225995,1163455746941612,2817121235116652,5068921048801932,1411885572435106,2819260455988322,582914127569484,2537786821454850,2819261798165570,4647790690175616,585319310426186,2326945728823402,587182580696640,1167724946917028,4646126139999366],0,[[897,898,900,904,912,928,960],[909,924,932,937,945,963,966,970,978,994],[925,941,949,953,956,975,990,998,1003,1011]]),
(14,[1056,1216,1220],8126,8717945189,[1218086372445069033615,5312723119942580846767,1475800371925772959753,2656552216664450596913,1217787240521758146567,2951781186637322780711,2954078004856762933319,4871385130009919226049,611340165634303983683,611127256203448025251,614513963123232735405,217746671454478,1414015322474510,2539915229317166,4650977554647246,296894555278952,2821373252652584,1414016069060718,5073176824434344,2328797881880328,59416997274758,217746671674630,4650977554867398,585301609424612,1165843748890116,5071309050750660,1165844268983940,585302129518244,2326930628290308,212833229358350,4646064112551118,1167707764968970,1164538599197316,5632953854479044,1409102626966126,2323896301275694,2325624958503684,2539901002728554,2818203567816744,5070003381502152,214560360399112,587183326005408,1167724946457104,5073190248317648,587183327085232,1165862599987202,4649115436781762],0,[[513,514,516,520,528,544,576,640,768],[518,522,525,530,532,536,545,556,588,593,608,642,652,657,688,704,771,780,784,802,834,896],[534,538,557,605,620,625,654,659,669,689,690,700,716,721,724,752,783,796,803,814,818,846,851,866,899,908,913,916,930,944,962],[637,671,701,702,755,757,761,764,815,830,863,878,883,911,919,942,947,949,954,956,974,979,982,989,1010]])]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem hornChecks : hornSamples.all verifyOrder = true := by decide +kernel
theorem hornImpossible {s : OrderSample} (h : s∈hornSamples) :
    Impossible false target s.1 (orderState s).toFinset :=
  order_sound (List.all_eq_true.mp hornChecks s h)
end PEqualNP.Outside.L_meta_9822.Ranked

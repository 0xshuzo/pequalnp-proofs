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
theorem shrink_only {S R : Finset Sig} {T a p n} (sub : S⊆R) (h : onlyWire R T a p n) :
    onlyWire S T a p n := ⟨h.1,h.2.1,fun v hv => h.2.2 v (sub hv)⟩
theorem common_difference {ws S T a b t f} (ok : excluded ws T a b t=true)
    (sub : S⊆ws.toFinset) (law : orderLaw S T f) : f a ≠ f b := by
  simp only [excluded,Bool.and_eq_true,bne_iff_ne] at ok
  exact law.1 ok.1.1.1.1 (shrink_only sub (kwWireB_sound ok.1.1.1.2))
    (shrink_only sub (kwWireB_sound ok.1.1.2)) (shrink_only sub (kwWireB_sound ok.1.2))
    (shrink_only sub (kwWireB_sound ok.2))
abbrev PrefixPage := List Nat × Nat × Nat × Nat × Nat × List (Nat × Nat)
def groupBank (g : PrefixPage) := g.1.foldl (fun bank d => bank++[child bank d]) raw
def family (g : PrefixPage) :=
  let bank := groupBank g
  g.2.2.2.2.2.map (fun (d,m) => liveList m (bank++[child bank d]))
abbrev Bucket := Nat × List PrefixPage
def anchor (v : Bucket) : PrefixPage := v.2.headD ([],0,0,0,0,[])
def allStates (v : Bucket) :=
  v.2.flatMap (fun g => (family g).map (fun ws => (g.2.1,ws)))
def bucketCheck (v : Bucket) :=
  let ref := anchor v
  let bank := groupBank ref
  let a := bank.getD ref.2.2.1 zero
  let b := bank.getD ref.2.2.2.1 zero
  let states := allStates v
  excluded ((states.map Prod.snd).flatten.eraseDups) target a b v.1 &&
    states.all (fun (k,ws) => (ws.contains a && ws.contains b) && decide (k+1≤ws.toFinset.card))
theorem bucket_sound {v : Bucket} (ok : bucketCheck v=true) {k : Nat} {ws : List Sig}
    (belong : (k,ws)∈allStates v) : ∀ q, q≤k → ¬Live false target q ws.toFinset := by
  let ref := anchor v
  let a := (groupBank ref).getD ref.2.2.1 zero
  let b := (groupBank ref).getD ref.2.2.2.1 zero
  let states := allStates v
  let pool := (states.map Prod.snd).flatten.eraseDups
  change (excluded pool target a b v.1 && states.all
    (fun (t,l) => (l.contains a && l.contains b) && decide (t+1≤l.toFinset.card)))=true at ok
  have both := Bool.and_eq_true_iff.mp ok
  have data := List.all_eq_true.mp both.2 (k,ws) belong
  simp only [Bool.and_eq_true,List.contains_eq_mem,decide_eq_true_eq] at data
  have sub : ws.toFinset⊆pool.toFinset := by
    intro w hw
    have wm : ws∈states.map Prod.snd := List.mem_map.mpr ⟨(k,ws),belong,rfl⟩
    have fm : w∈(states.map Prod.snd).flatten := List.mem_flatten.mpr ⟨ws,wm,List.mem_toFinset.mp hw⟩
    apply List.mem_toFinset.mpr
    simpa [pool] using fm
  intro q hq run
  obtain ⟨count,f,mass,limit,law⟩ := order_live run
  have ha := limit _ (List.mem_toFinset.mpr data.1.1)
  have hb := limit _ (List.mem_toFinset.mpr data.1.2)
  have ab := common_difference both.1 sub law
  have width := data.2
  omega
def block0 : Bucket := (148692184136360966,[([4129,1188,1252,1317,1286],11,1,2,0,[(1319,64847),(1320,64719)]),
([4129,1188,1252,1317],12,1,2,0,[(1286,32719),(1446,32719),(1448,32719),(428,32719)]),
([4129,1188,1252,1317,326,1319],10,1,2,0,[(1480,112975),(1485,112975),(1518,112975)]),
([4129,1188,1252,1317,326,1320],10,1,2,0,[(1416,125135),(1480,112847)]),
([4129,1188,1252,1317,326],11,1,2,0,[(1320,63951),(1416,60367),(1480,48079),(1485,48079)]),
([4129,1188,1252,1317,1446],11,1,2,0,[(1319,64847)]),
([4129,1188,1252,1317,1319],11,1,2,0,[(1478,64847),(1448,64847),(1480,64847),(428,64847)]),
([4129,1188,1252,1317,1319,362],10,1,2,0,[(1512,96591),(1518,96591)]),
([4129,1188,1252,1317,1319,394],10,1,2,0,[(1512,96591),(1517,96591)]),
([4129,1188,1252,1317,1319,426],10,1,2,0,[(1512,96591)]),
([4129,1188,1252,1317,1320,1416],10,1,2,0,[(426,125135),(458,125135)]),
([4129,1188,1252,1317,1320],11,1,2,0,[(362,63951),(394,63951),(426,63951),(458,63951)]),
([4129,1188,1252,1317,1320,394],10,1,2,0,[(1512,96463)]),
([4129,1188,1252,1317,1416],11,1,2,0,[(426,60367)]),
([4129,1188,1252,1317,362],11,1,2,0,[(1480,48079)]),
([4129,1188,1252,1317,394],11,1,2,0,[(1480,48079),(1485,48079)]),
([4129,1188,1252,1317,426],11,1,2,0,[(1480,48079)]),
([4129,1188,1252,1286],12,1,2,0,[(1319,32623),(1320,32495),(1449,24559),(427,24559),(428,24559)]),
([4129,1188,1252,1318,1320],11,1,2,0,[(1416,60655)]),
([4129,1188,1252,1318],12,1,2,0,[(1320,32239),(1416,28655),(427,24559),(428,24559)]),
([4129,1188,1252,326,1319],11,1,2,0,[(1448,56175),(1485,56175)]),
([4129,1188,1252,326,1320,1416],10,1,2,0,[(1449,116975)]),
([4129,1188,1252,326,1320],11,1,2,0,[(1416,60143),(1448,56047),(1449,55791),(1485,39919)]),
([4129,1188,1252,326],12,1,2,0,[(1320,31727)]),
([4129,1188,1252,326,1416],11,1,2,0,[(1449,52207)]),
([4129,1188,1252,1319],12,1,2,0,[(1446,32623),(1448,32623)]),
([4129,1188,1252,1319,362],11,1,2,0,[(1480,47983),(1485,47983)]),
([4129,1188,1252,1319,394],11,1,2,0,[(1480,47983)]),
([4129,1188,1252,1320,1416],11,1,2,0,[(426,60143)]),
([4129,1188,1252,1320,362],11,1,2,0,[(1485,39919)]),
([4129,1188,1252,1320],12,1,2,0,[(362,31727),(394,31727),(426,31727),(427,24559),(428,24559)]),
([4129,1188,1252,1320,394],11,1,2,0,[(1480,47855),(1485,39919)]),
([4129,1188,1284,1317,1254],11,1,2,0,[(1319,64847),(1320,64719)]),
([4129,1188,1284,1317],12,1,2,0,[(1254,32719),(1446,32719),(1447,32719),(428,32719)]),
([4129,1188,1284,1317,326,1319],10,1,2,0,[(1479,112975)]),
([4129,1188,1284,1317,326],11,1,2,0,[(1319,63951),(1479,48079),(1485,48079)]),
([4129,1188,1284,1317,326,1479],10,1,2,0,[(1320,112847)]),
([4129,1188,1284,1317,326,1320],10,1,2,0,[(1485,112847),(1518,112847)]),
([4129,1188,1284,1317,1446],11,1,2,0,[(1320,64719)]),
([4129,1188,1284,1317,1319],11,1,2,0,[(362,63951),(394,63951),(426,63951)]),
([4129,1188,1284,1317,327,1320],10,1,2,0,[(1485,112847),(1518,112847)]),
([4129,1188,1284,1317,327],11,1,2,0,[(1485,48079)]),
([4129,1188,1284,1317,1447],11,1,2,0,[(1320,64719)]),
([4129,1188,1284,1317,1320],11,1,2,0,[(1478,64719),(1479,64719),(459,64719),(428,64719)]),
([4129,1188,1284,1317,1320,1479],10,1,2,0,[(458,112847)]),
([4129,1188,1284,1317,1320,362],10,1,2,0,[(1511,96463),(1518,96463)]),
([4129,1188,1284,1317,1320,394],10,1,2,0,[(1511,96463),(1517,96463)]),
([4129,1188,1284,1317,1320,426],10,1,2,0,[(1511,96463)]),
([4129,1188,1284,1317,1320,458],10,1,2,0,[(1511,96463),(459,112847)]),
([4129,1188,1284,1317,362],11,1,2,0,[(1479,48079)]),
([4129,1188,1284,1317,394],11,1,2,0,[(1479,48079),(1485,48079)]),
([4129,1188,1284,1317,426],11,1,2,0,[(1479,48079)]),
([4129,1188,1284,1254,1318],11,1,2,0,[(1320,64687)]),
([4129,1188,1284,1254],12,1,2,0,[(1318,32687),(1319,32623),(1320,32495),(1449,24559),(427,24559),(428,24559)]),
([4129,1188,1284,1318],12,1,2,0,[(427,24559),(428,24559)]),
([4129,1188,1284,326,1319],11,1,2,0,[(1447,56175),(1485,39919)]),
([4129,1188,1284,326],12,1,2,0,[(1319,31727)]),
([4129,1188,1284,326,1447],11,1,2,0,[(1320,56047),(459,39919)]),
([4129,1188,1284,326,1320],11,1,2,0,[(1485,56047)]),
([4129,1188,1284,1319,362],11,1,2,0,[(1485,39919)]),
([4129,1188,1284,1319],12,1,2,0,[(362,31727),(394,31727),(427,24559),(428,24559)]),
([4129,1188,1284,1319,394],11,1,2,0,[(1485,39919)]),
([4129,1188,1284,327,1320],11,1,2,0,[(1485,56047)]),
([4129,1188,1284,1320],12,1,2,0,[(1446,32495),(1447,32495),(427,32495)]),
([4129,1188,1284,1320,1447],11,1,2,0,[(426,56047)]),
([4129,1188,1284,1320,362],11,1,2,0,[(1479,47855),(1485,47855)]),
([4129,1188,1284,1320,394],11,1,2,0,[(1479,47855)]),
([4129,1188,1284,1320,426],11,1,2,0,[(1479,47855),(427,56047)]),
([4129,1188,1317,1254,1414],11,1,2,0,[(1319,64799)]),
([4129,1188,1317,1254],12,1,2,0,[(1414,32671),(1287,32607),(1320,32223),(1448,24543),(427,24543),(428,24543),(1452,24543)]),
([4129,1188,1317,1254,1287],11,1,2,0,[(1320,64607),(1481,48479)]),
([4129,1188,1317,1254,1320],11,1,2,0,[(1448,56543)]),
([4129,1188,1317,1254,1448],11,1,2,0,[(460,36831)]),
([4129,1188,1317,1286],12,1,2,0,[(1319,32223),(427,24543),(428,24543),(1452,24543)]),
([4129,1188,1317,326,1287,1447],10,1,2,0,[(1320,120927),(1481,104799)]),
([4129,1188,1317,326,1287],11,1,2,0,[(1447,56159),(1320,63711),(1481,47583),(460,43999),(1485,39903)]),
([4129,1188,1317,326,1287,1320],10,1,2,0,[(1485,104671)]),
([4129,1188,1317,326,1287,1485],10,1,2,0,[(492,68575)]),
([4129,1188,1317,326],12,1,2,0,[(1287,31711),(1383,31711),(1415,31711),(1384,31711),(1416,31711)]),
([4129,1188,1317,326,1319],11,1,2,0,[(1448,55775),(1452,55775),(1485,55775)]),
([4129,1188,1317,326,1415],11,1,2,0,[(1485,39903)]),
([4129,1188,1317,326,1447],11,1,2,0,[(1320,55775),(459,39903),(460,39903)]),
([4129,1188,1317,326,1320],11,1,2,0,[(1452,55775),(1485,55775)]),
([4129,1188,1317,326,1416],11,1,2,0,[(1452,52191),(1485,39903)]),
([4129,1188,1317,1382],12,1,2,0,[(1319,32223),(1320,32223)]),
([4129,1188,1317,1382,1320],11,1,2,0,[(461,40415)]),
([4129,1188,1317,1414],12,1,2,0,[(1319,32223),(1320,32223),(1416,28639)]),
([4129,1188,1317,1287,1444,1320],10,1,2,0,[(426,121039)]),
([4129,1188,1317,1287,1444],11,1,2,0,[(1320,64719),(1449,56783),(426,56271),(428,53199)]),
([4129,1188,1317,1287,1444,426],10,1,2,0,[(1513,88527)]),
([4129,1188,1317,1287],12,1,2,0,[(1444,32719),(1416,32479),(1449,32223),(362,31711),(394,31711),(426,31711),(427,24543),(428,28639),(428,24543),(1452,24543)]),
([4129,1188,1317,1287,1320],11,1,2,0,[(362,63711),(394,63711),(426,63711),(458,63711)]),
([4129,1188,1317,1287,1320,426],10,1,2,0,[(1508,96463)]),
([4129,1188,1317,1287,1449,426],10,1,2,0,[(1508,88527)]),
([4129,1188,1317,1287,1449],11,1,2,0,[(426,55775),(362,55775),(394,55775),(458,55775)]),
([4129,1188,1317,1287,362],11,1,2,0,[(428,52191),(1485,39903)]),
([4129,1188,1317,1287,394],11,1,2,0,[(1480,47839),(428,52191),(1485,39903)]),
([4129,1188,1317,1287,426,1476],10,1,2,0,[(428,101327)]),
([4129,1188,1317,1287,426],11,1,2,0,[(1476,48079),(1481,47583),(428,52191)]),
([4129,1188,1317,1287,427],11,1,2,0,[(1481,40415)]),
([4129,1188,1317,1287,428],11,1,2,0,[(1476,53199),(458,52191)]),
([4129,1188,1317,1287,428,458],10,1,2,0,[(1508,84943)]),
([4129,1188,1317,1319],12,1,2,0,[(1446,32223),(1384,32223),(1416,32223),(1448,32223),(1451,32223)]),
([4129,1188,1317,1319,362],11,1,2,0,[(1480,47583),(1485,47583)]),
([4129,1188,1317,1319,394],11,1,2,0,[(1480,47583)]),
([4129,1188,1317,327,1444],11,1,2,0,[(1416,56271)]),
([4129,1188,1317,327,1320,1448],10,1,2,0,[(1508,121039)]),
([4129,1188,1317,327,1320],11,1,2,0,[(1452,55775),(1485,55775)]),
([4129,1188,1317,327,1384],11,1,2,0,[(1449,55775)]),
([4129,1188,1317,327],12,1,2,0,[(1384,31711),(1416,31711)]),
([4129,1188,1317,327,1416],11,1,2,0,[(1448,56031),(1449,55775),(1485,39903)]),
([4129,1188,1317,327,1448,1476],10,1,2,0,[(1481,104911)]),
([4129,1188,1317,327,1448],11,1,2,0,[(1476,56271),(1481,55775),(459,39903),(460,39903)]),
([4129,1188,1317,327,1448,459],10,1,2,0,[(1513,72159)]),
([4129,1188,1317,1383],12,1,2,0,[(1320,32223),(394,31711)]),
([4129,1188,1317,1415],12,1,2,0,[(1320,32223),(362,31711),(394,31711),(426,31711)]),
([4129,1188,1317,1320],12,1,2,0,[(1446,32223),(1447,32223),(427,32223),(1451,32223)]),
([4129,1188,1317,1320,1447],11,1,2,0,[(426,55775)]),
([4129,1188,1317,1320,362],11,1,2,0,[(1479,47583),(1485,47583)]),
([4129,1188,1317,1320,394],11,1,2,0,[(1479,47583)]),
([4129,1188,1317,1320,426],11,1,2,0,[(1479,47583),(427,55775)]),
([4129,1188,1317,1384],12,1,2,0,[(394,31711)]),
([4129,1188,1317,1416],12,1,2,0,[(362,31711),(394,31711),(426,31711)]),
([4129,1188,1317,362,1447],11,1,2,0,[(1484,39903)]),
([4129,1188,1317,362,1448],11,1,2,0,[(1484,39903)]),
([4129,1188,1317,394,1447],11,1,2,0,[(459,39903)]),
([4129,1188,1317,394,1448],11,1,2,0,[(459,39903)]),
([4129,1188,1254,1318,1287],11,1,2,0,[(1320,64575)]),
([4129,1188,1254,1318],12,1,2,0,[(1287,32575),(1320,32191)]),
([4129,1188,1254,1287],12,1,2,0,[(1444,32623),(1320,32383),(1449,24447)]),
([4129,1188,1254,1320],12,1,2,0,[(1416,28415),(428,20479),(1452,20479)]),
([4129,1188,1254],13,1,2,0,[(1320,16383),(1384,16383),(1416,16383),(1385,16383),(1417,16383),(395,16383),(1419,16383)]),
([4129,1188,1254,1384],12,1,2,0,[(428,20479)]),
([4129,1188,1254,1416],12,1,2,0,[(427,20479)]),
([4129,1188,1254,1385],12,1,2,0,[(428,20479)]),
([4129,1188,1254,1417],12,1,2,0,[(427,20479)]),
([4129,1188,1254,395],12,1,2,0,[(1448,20479),(1449,20479)]),
([4129,1188,1286],13,1,2,0,[(1319,16383),(1383,16383),(1415,16383),(1385,16383),(1417,16383),(1419,16383)]),
([4129,1188,1286,1417],12,1,2,0,[(427,20479)]),
([4129,1188,1286,395],12,1,2,0,[(1447,20479),(1449,20479)]),
([4129,1188,1318,1287],12,1,2,0,[(1320,31999)]),
([4129,1188,1318],13,1,2,0,[(1287,16383),(1383,16383),(1415,16383),(1384,16383),(1416,16383),(1419,16383)]),
([4129,1188,1318,395],12,1,2,0,[(1447,20479),(1448,20479)]),
([4129,1188,326,1287,1444],11,1,2,0,[(1415,60271),(1452,52207)]),
([4129,1188,326,1287],12,1,2,0,[(1444,31727),(1320,31487),(1417,27647),(1449,23551),(427,23551),(1452,27647)]),
([4129,1188,326,1287,1415],11,1,2,0,[(1320,60031),(1449,52095)]),
([4129,1188,326,1287,1320],11,1,2,0,[(1417,59647),(1452,51967)]),
([4129,1188,326,1287,1417],11,1,2,0,[(1485,35839)]),
([4129,1188,326,1287,427],11,1,2,0,[(1484,35839)]),
([4129,1188,326,1287,1452],11,1,2,0,[(459,35839)])])
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem done0 : bucketCheck block0 = true := by decide +kernel
def block1 : Bucket := (180163507378143265,[([4129,1188,1252,1286],12,0,5,0,[(1385,30703)]),
([4129,1188,1252,326,1448],11,0,5,0,[(1385,54255)])])
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem done1 : bucketCheck block1 = true := by decide +kernel
def block2 : Bucket := (27058097889587217,[([4129,1188,1284,1317,1382],11,0,12,0,[(1319,62927)])])
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem done2 : bucketCheck block2 = true := by decide +kernel
def block3 : Bucket := (180162893197819937,[([4129,1188,1284,1382],12,0,5,0,[(1319,30703)])])
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem done3 : bucketCheck block3 = true := by decide +kernel
def block4 : Bucket := (27058295458082833,[([4129,1188,1317,1254,1319],11,0,4,0,[(1451,62815)]),
([4129,1188,1317,1254,1320],11,0,4,0,[(1451,54751)]),
([4129,1188,1317,1254],12,0,4,0,[(1451,30687)]),
([4129,1188,1317,1286,1383],11,0,4,0,[(1320,62687)]),
([4129,1188,1317,1286],12,0,4,0,[(1383,30687)]),
([4129,1188,1317,1414],12,0,4,0,[(1383,30687)]),
([4129,1188,1317,1383,1320],11,0,4,0,[(426,61919)]),
([4129,1188,1317,1383],12,0,4,0,[(1416,30687)]),
([4129,1188,1317,1383,426],11,0,4,0,[(1484,46047)]),
([4129,1188,1254,1318],12,0,4,0,[(1419,30655)]),
([4129,1188,1254,1287],12,0,4,0,[(1419,30591)]),
([4129,1188,1254,1319],12,0,4,0,[(1419,30591)]),
([4129,1188,1254,1320],12,0,4,0,[(1419,26623)]),
([4129,1188,1254,1416],12,0,4,0,[(1419,26623)]),
([4129,1188,1254,1417],12,0,4,0,[(1419,26623)]),
([4129,1188,1254,395],12,0,4,0,[(1419,26623)]),
([4129,1188,1254,1419],12,0,4,0,[(425,30207)]),
([4129,1188,1286,1383],12,0,4,0,[(395,26623),(1320,30463),(1417,26623),(428,26623)]),
([4129,1188,1318,1383],12,0,4,0,[(395,26623),(1320,30207),(428,26623)])])
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem done4 : bucketCheck block4 = true := by decide +kernel
def block5 : Bucket := (27058097891684369,[([4129,1188,1317,326,1287,1320],10,0,4,0,[(1451,119007)]),
([4129,1188,1317,326,1287,1481],10,0,4,0,[(1451,102879)]),
([4129,1188,1317,326,1287],11,0,4,0,[(1451,54239)]),
([4129,1188,1317,326,1415],11,0,4,0,[(1451,54239)]),
([4129,1188,1317,326,1416],11,0,4,0,[(1451,54239)]),
([4129,1188,326,1287,1320],11,0,4,0,[(1419,58111)]),
([4129,1188,326,1287,1449],11,0,4,0,[(1419,50175)])])
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem done5 : bucketCheck block5 = true := by decide +kernel
def block6 : Bucket := (27058297607663633,[([4129,1188,1317,326,1319,1447],10,0,4,0,[(1515,119135)]),
([4129,1188,1317,326,1383,1320],10,0,4,0,[(1448,119007)]),
([4129,1188,1317,326,1383],11,0,4,0,[(1320,61919),(1448,54239),(1452,54239)]),
([4129,1188,1317,326,1447],11,0,4,0,[(1483,54239)]),
([4129,1188,1317,1383,362],11,0,4,0,[(1480,46047)]),
([4129,1188,1317,1383,1320],11,0,4,0,[(394,61919),(458,61919)]),
([4129,1188,1317,1383,394],11,0,4,0,[(1480,46047)]),
([4129,1188,1317,1383,426],11,0,4,0,[(1480,46047)]),
([4129,1188,326,1287,1415],11,0,4,0,[(1483,58239)]),
([4129,1188,326,1319,1415],11,0,4,0,[(1483,58239)])])
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem done6 : bucketCheck block6 = true := by decide +kernel
def block7 : Bucket := (27058712072007697,[([4129,1188,1317,326,1416,1451],10,0,4,0,[(494,70623)]),
([4129,1188,1317,327,1416,1451],10,0,4,0,[(494,70623)]),
([4129,1188,326,1287,1415],11,0,4,0,[(1385,58239),(427,58239),(1451,58239),(459,58239)]),
([4129,1188,326,1287,1385,1452],10,0,4,0,[(494,66559)]),
([4129,1188,326,1287,1385],11,0,4,0,[(1452,50175),(461,37887)]),
([4129,1188,326,1287,1385,461],10,0,4,0,[(1516,66559)]),
([4129,1188,326,1287],12,0,4,0,[(1385,29695),(427,29695),(1451,29695)]),
([4129,1188,326,1287,1417,427],10,0,4,0,[(1518,66559)]),
([4129,1188,326,1287,1417],11,0,4,0,[(427,50175),(1451,50175)]),
([4129,1188,326,1287,1417,1485],10,0,4,0,[(491,66559)]),
([4129,1188,326,1287,1449,1419],10,0,4,0,[(494,66559)]),
([4129,1188,326,1287,1449,459],10,0,4,0,[(1516,66559)]),
([4129,1188,326,1287,1449],11,0,4,0,[(459,37887)]),
([4129,1188,326,1287,1419],11,0,4,0,[(461,41983)]),
([4129,1188,326,1287,1419,461],10,0,4,0,[(1513,66559)]),
([4129,1188,326,1287,427],11,0,4,0,[(1452,50175),(1484,41983),(1481,37887),(1484,50175)]),
([4129,1188,326,1287,1451],11,0,4,0,[(1452,50175)]),
([4129,1188,326,1287,1452],11,0,4,0,[(459,41983),(459,50175),(1483,50175)]),
([4129,1188,326,1287,1452,459],10,0,4,0,[(1513,66559)]),
([4129,1188,326,1319,1415],11,0,4,0,[(1384,58239),(1451,58239),(459,58239)])])
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem done7 : bucketCheck block7 = true := by decide +kernel
def block8 : Bucket := (27058097889587217,[([4129,1188,1317,1382,1287],11,0,4,0,[(1320,62687),(1481,46559)]),
([4129,1188,1317,1382],12,0,4,0,[(1287,30687),(1415,30687),(1416,30687)]),
([4129,1188,1317,1382,1319],11,0,4,0,[(461,46559)]),
([4129,1188,1317,1382,1320],11,0,4,0,[(461,46559)])])
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem done8 : bucketCheck block8 = true := by decide +kernel
def block9 : Bucket := (27058712069910545,[([4129,1188,1317,1382,1416],11,0,4,0,[(461,38879)]),
([4129,1188,1317,1383,1416],11,0,4,0,[(461,38879)]),
([4129,1188,1254,1318],12,0,4,0,[(1384,30655),(395,30655),(1451,30655)]),
([4129,1188,1254,1287],12,0,4,0,[(1385,30591),(395,30591),(427,30591),(1451,30591)]),
([4129,1188,1254,1319],12,0,4,0,[(1384,30591),(395,30591),(1451,30591)]),
([4129,1188,1254,1320,395],11,0,4,0,[(1480,42751),(461,34815),(1485,34815)]),
([4129,1188,1254,1320],12,0,4,0,[(395,26623),(427,22527),(1451,22527)]),
([4129,1188,1254,1320,1419],11,0,4,0,[(461,34815)]),
([4129,1188,1254,1320,427],11,0,4,0,[(1479,38783),(1484,34815)]),
([4129,1188,1254,1320,1451],11,0,4,0,[(460,34815)]),
([4129,1188,1254,1320,1452],11,0,4,0,[(459,34815)]),
([4129,1188,1254,1384],12,0,4,0,[(395,26623),(1417,26623),(428,26623),(428,22527),(1452,22527)]),
([4129,1188,1254,1384,1417],11,0,4,0,[(461,34815)]),
([4129,1188,1254,1384,428],11,0,4,0,[(1481,34815)]),
([4129,1188,1254,1416],12,0,4,0,[(395,26623),(427,22527),(1385,26623),(427,26623),(1451,26623)]),
([4129,1188,1254,1416,1385],11,0,4,0,[(461,34815)]),
([4129,1188,1254,1416,427],11,0,4,0,[(1481,34815)]),
([4129,1188,1254,1385],12,0,4,0,[(395,26623),(428,26623),(428,22527),(1452,22527)]),
([4129,1188,1254,1385,428],11,0,4,0,[(1480,34815)]),
([4129,1188,1254,1417],12,0,4,0,[(395,26623),(427,22527),(427,26623),(1451,26623)]),
([4129,1188,1254,1417,427],11,0,4,0,[(1480,34815)]),
([4129,1188,1254,395],12,0,4,0,[(1448,22527),(1449,22527),(1448,26623),(1449,26623)]),
([4129,1188,1286,1319],12,0,4,0,[(1419,26623),(1451,22527)]),
([4129,1188,1286,1383,1417],11,0,4,0,[(461,34815)]),
([4129,1188,1286,1383],12,0,4,0,[(1452,22527)]),
([4129,1188,1286,1415],12,0,4,0,[(1419,26623),(427,22527)]),
([4129,1188,1286,1320],12,0,4,0,[(1419,30463),(427,30463),(1451,30463)]),
([4129,1188,1286,1385],12,0,4,0,[(395,26623),(428,26623),(1452,22527)]),
([4129,1188,1286,1417],12,0,4,0,[(1419,26623),(427,22527),(427,26623),(1451,26623)]),
([4129,1188,1286,1417,427],11,0,4,0,[(1479,34815)]),
([4129,1188,1318,1287,1419],11,0,4,0,[(461,34815)]),
([4129,1188,1318,1287],12,0,4,0,[(1419,26623),(427,22527),(1451,22527)]),
([4129,1188,1318,1287,427],11,0,4,0,[(1478,38847),(1484,34815)]),
([4129,1188,1318,1383],12,0,4,0,[(1452,22527)]),
([4129,1188,1318,1415],12,0,4,0,[(1419,26623),(427,22527)]),
([4129,1188,1318,1320],12,0,4,0,[(1419,30207),(427,30207),(1451,30207)]),
([4129,1188,1318,1384],12,0,4,0,[(395,26623),(428,26623),(1452,22527)]),
([4129,1188,1318,1416],12,0,4,0,[(1419,26623),(427,22527)])])
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem done9 : bucketCheck block9 = true := by decide +kernel
def block10 : Bucket := (148692183061570566,[([4129,1188,1317,1287,428,1472],10,1,2,0,[(1476,102350),(458,101342)]),
([4129,1188,1317,1287,428,1472,458],9,1,2,0,[(1540,166862)]),
([4129,1188,1317,1287,428],11,1,2,0,[(1472,53214)])])
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem done10 : bucketCheck block10 = true := by decide +kernel
def block11 : Bucket := (148692183061569542,[([4129,1188,1317,1287,428,1472,458],9,1,2,0,[(491,197598)]),
([4129,1188,1317,1287,428,1472],10,1,2,0,[(491,83934)])])
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem done11 : bucketCheck block11 = true := by decide +kernel
def block12 : Bucket := (148692184135312390,[([4129,1188,1317,1287,428,458],10,1,2,0,[(1504,84958)])])
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem done12 : bucketCheck block12 = true := by decide +kernel
def block13 : Bucket := (27058295460179985,[([4129,1188,1317,327,1416],11,0,4,0,[(1451,54239)])])
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem done13 : bucketCheck block13 = true := by decide +kernel
def block14 : Bucket := (27058297607663635,[([4129,1188,1317,1383,1320],11,0,4,0,[(362,61919)])])
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem done14 : bucketCheck block14 = true := by decide +kernel
def block15 : Bucket := (360295395332739138,[([4129,1188,1317,1384,394],11,1,6,0,[(1474,48091)]),
([4129,1188,1317,1416,394],11,1,6,0,[(1474,48091)])])
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem done15 : bucketCheck block15 = true := by decide +kernel
def allBlocks : List Bucket := [block0,block1,block2,block3,block4,block5,block6,block7,block8,block9,block10,block11,block12,block13,block14,block15]
theorem block_done (v : Bucket) (mem : v∈allBlocks) : bucketCheck v = true := by
  simp only [allBlocks,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact done0
  · exact done1
  · exact done2
  · exact done3
  · exact done4
  · exact done5
  · exact done6
  · exact done7
  · exact done8
  · exact done9
  · exact done10
  · exact done11
  · exact done12
  · exact done13
  · exact done14
  · exact done15
theorem all_closed (v : Bucket) (hv : v∈allBlocks) {k : Nat} {ws : List Sig} (mem : (k,ws)∈allStates v) : ∀ q, q≤k → ¬Live false target q ws.toFinset := bucket_sound (block_done v hv) mem
end PEqualNP.Outside.L_meta_9822.Ranked

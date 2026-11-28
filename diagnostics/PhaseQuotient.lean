import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9755.Phase
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

def canonical (a : Sig) : Sig := if a.getLsbD 0 then ~~~a else a
def phase (p : Bool) (a : Sig) : Sig := if p then ~~~a else a
def product (p q : Bool) (a b : Sig) := canonical ((phase p a) &&& (phase q b))
def opcode (p q : Bool) : Nat := if p then (if q then 1 else 3) else (if q then 2 else 0)
def normal (a : Sig) := a.getLsbD 0=false

theorem product_eq (p q : Bool) (a b : Sig) (ha : normal a) (hb : normal b) :
    product p q a b=bin (opcode p q) a b := by
  unfold normal at ha hb
  cases p <;> cases q <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp [product,phase,canonical,opcode,bin,ha,hb,hi] <;> cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem product_normal (p q : Bool) (a b : Sig) : normal (product p q a b) := by
  unfold product canonical normal
  split <;> simp_all

theorem opcode_allowed (p q : Bool) : allowed true (opcode p q) := by
  cases p <;> cases q <;> decide

theorem opcode_surj {d : Nat} (h : allowed true d) : ∃ p q, opcode p q=d := by
  obtain h|h|h|h := allowed_four h
  · exact ⟨false,false,h.symm⟩
  · exact ⟨true,true,h.symm⟩
  · exact ⟨false,true,h.2.symm⟩
  · exact ⟨true,false,h.2.symm⟩

def Aig (T : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={T} ∧ proper T
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (p q : Bool),
      S=insert a (insert b U) ∧ proper a ∧ proper b ∧ a≠b ∧
      product p q a b ∉ insert a (insert b U) ∧ Aig T k (insert (product p q a b) U)

theorem quotient_iff (T : Sig) (k : Nat) (S : Finset Sig) (rooted : ∀ v∈S,normal v) :
    Live true T k S ↔ Aig T k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    constructor
    · rintro ⟨U,a,b,d,hd,rfl,pa,pb,ne,fresh,tail⟩
      obtain ⟨p,q,rfl⟩ := opcode_surj hd
      have he := product_eq p q a b (rooted a (by simp)) (rooted b (by simp))
      refine ⟨U,a,b,p,q,rfl,pa,pb,ne,he.symm ▸ fresh,?_⟩
      have nextNorm : ∀ v∈insert (product p q a b) U, normal v := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact product_normal p q a b
        · exact rooted v (by simp [hv])
      exact (ih _ nextNorm).mp (he.symm ▸ tail)
    · rintro ⟨U,a,b,p,q,rfl,pa,pb,ne,fresh,tail⟩
      have he := product_eq p q a b (rooted a (by simp)) (rooted b (by simp))
      refine ⟨U,a,b,opcode p q,opcode_allowed p q,rfl,pa,pb,ne,he ▸ fresh,?_⟩
      rw [←he]
      apply (ih _ ?_).mpr tail
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact product_normal p q a b
      · exact rooted v (by simp [hv])

def pin (j : Nat) : Sig := BitVec.ofNat 1024 ((((2:Nat)^1024-1)/(2^(2^j)+1)) <<< (2^j))
def initial := ((List.range 10).map pin).toFinset
def graph : Sig :=
  (pin 0 &&& pin 4) ||| (pin 0 &&& pin 5) ||| (pin 1 &&& pin 2) ||| (pin 1 &&& pin 6) ||| (pin 2 &&& pin 3) ||| (pin 2 &&& pin 7) ||| (pin 3 &&& pin 4) ||| (pin 3 &&& pin 8) ||| (pin 4 &&& pin 9) ||| (pin 5 &&& pin 7) ||| (pin 5 &&& pin 8) ||| (pin 6 &&& pin 8) ||| (pin 6 &&& pin 9) ||| (pin 7 &&& pin 9)

theorem initial_normal (v : Sig) (hv : v∈initial) : normal v := by
  have hh : v∈(List.range 10).map pin := List.mem_toFinset.mp hv
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hh
  have lt := List.mem_range.mp hi
  interval_cases i <;> decide +kernel

theorem graph_census_iff (k : Nat) (S : Finset Sig) (hS : S ⊆ initial) :
    Live true graph k S ↔ Aig graph k S :=
  quotient_iff graph k S (fun v hv => initial_normal v (hS hv))

end PEqualNP.Outside.L_meta_9755.Phase

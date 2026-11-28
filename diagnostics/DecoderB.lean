import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_931.Code

def header (n : Nat) := List.replicate n true ++ [false]
def bits (width value : Nat) := (List.range width).map (fun h => value.testBit h)
def val : List Bool → Nat
  | [] => 0
  | b::l => b.toNat+2*val l
lemma bit_cons (w v:Nat) : bits (w+1) v = v.testBit 0 :: bits w (v/2) := by
  simp only [bits,List.range_succ_eq_map,List.map_cons,List.map_map]
  congr 1
  apply List.map_congr_left
  intro h _
  simp [Nat.testBit_succ]
lemma read_bits (w v:Nat) (h:v<2^w) : val (bits w v)=v := by
  induction w generalizing v with
  | zero => simp at h; subst h; rfl
  | succ w ih =>
    rw [bit_cons,val,ih (v/2) (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at h; exact h)]
    rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one v with h2 | h2 <;> simp [h2] <;> omega

def popHeader : List Bool → Nat × List Bool
  | [] => (0,[])
  | false::xs => (0,xs)
  | true::xs => let h := popHeader xs; (h.1+1,h.2)
theorem pop_header (n : Nat) (xs : List Bool) : popHeader (header n ++ xs) = (n,xs) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [header,List.replicate_succ,popHeader] using
      congrArg (fun h : Nat × List Bool => (h.1+1,h.2)) ih

def blocks {α : Type} (w : Nat) (f : List Bool → α) : Nat → List Bool → List α
  | 0, _ => []
  | k+1, xs => if xs=[] then [] else f (xs.take w) :: blocks w f k (xs.drop w)

theorem empty_blocks {α : Type} (w : Nat) (f : List Bool → α) (k : Nat) :
    blocks w f k [] = [] := by cases k <;> simp [blocks]

theorem blocks_roundtrip {α β : Type} (w : Nat) (hw : 0<w)
    (enc : α → List Bool) (f : List Bool → β) (g : α → β) (L : List α)
    (hlen : ∀ x ∈ L, (enc x).length=w) (hval : ∀ x ∈ L, f (enc x)=g x)
    (k : Nat) (hk : L.length ≤ k) : blocks w f k (L.flatMap enc) = L.map g := by
  induction L generalizing k with
  | nil => simp [empty_blocks]
  | cons x xs ih =>
    cases k with
    | zero => simp at hk
    | succ k =>
      have he := hlen x (List.mem_cons_self)
      have hn : enc x ++ xs.flatMap enc ≠ [] := by
        intro h
        have := congrArg List.length h
        simp [he] at this
        omega
      have hxt := ih (fun a ha => hlen a (List.mem_cons_of_mem _ ha))
          (fun a ha => hval a (List.mem_cons_of_mem _ ha)) k (by simpa using hk)
      simp [blocks,List.flatMap_cons,hn,List.take_left' he,List.drop_left' he,
        hval x List.mem_cons_self,hxt]

noncomputable def codeRow {n : Nat} (R : Finset (Fin n)) := R.toList.flatMap (fun i => bits (n.log2+1) i.val)

def decodeRow (n : Nat) (xs : List Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun u => u.val ∈ blocks (n.log2+1) val 3 xs)

theorem flat_width {α : Type} (w : Nat) (e : α → List Bool) (L : List α)
    (h : ∀ x ∈ L, (e x).length=w) : (L.flatMap e).length=L.length*w := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
    rw [h x List.mem_cons_self, ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]
    omega

theorem row_roundtrip {n : Nat} {R : Finset (Fin n)} (h : R.card=3) :
    decodeRow n (codeRow R)=R := by
  have hl : R.toList.length=3 := by simpa using h
  have hcode := blocks_roundtrip (n.log2+1) (by omega)
    (fun u : Fin n => bits (n.log2+1) u.val) val Fin.val R.toList
    (fun u _ => by simp [bits])
    (fun u _ => read_bits _ _ (lt_trans u.isLt Nat.lt_log2_self)) 3 hl.le
  ext u
  simp only [decodeRow,codeRow,hcode,Finset.mem_filter,Finset.mem_univ,true_and,List.mem_map]
  constructor
  · rintro ⟨v,hv,hEq⟩
    have e : v=u := Fin.ext hEq
    simpa [e] using hv
  · intro hu
    exact ⟨u,by simpa using hu,rfl⟩

def parseFamily (n : Nat) (xs : List Bool) : Finset (Finset (Fin n)) :=
  (blocks (3*(n.log2+1)) (decodeRow n) xs.length xs).toFinset

theorem family_roundtrip {n : Nat} (H : Finset (Finset (Fin n))) (hh : ∀ R ∈ H, R.card=3) :
    parseFamily n (H.toList.flatMap codeRow)=H := by
  let w := n.log2+1
  have hr (R : Finset (Fin n)) (hR : R ∈ H.toList) : (codeRow R).length=3*w := by
    rw [codeRow,flat_width w _ _ (fun _ _ => by simp [bits,w])]
    simp [hh R (by simpa using hR)]
  have hl := flat_width (3*w) codeRow H.toList hr
  have hk : H.toList.length ≤ (H.toList.flatMap codeRow).length := by
    rw [hl]
    exact Nat.le_mul_of_pos_right _ (by dsimp [w]; omega)
  have hrtrip := blocks_roundtrip (3*w) (by dsimp [w]; omega)
    codeRow (decodeRow n) id H.toList hr (fun R hR => row_roundtrip (hh R (by simpa using hR)))
    _ hk
  simpa [parseFamily,w] using congrArg List.toFinset hrtrip

def outputFor (n t : Nat) (H : Finset (Finset (Fin n))) : List Bool :=
  (List.range (n/2+1)).flatMap fun s => bits t
    ((Finset.univ.filter (fun N : Finset (Finset (Fin n)) =>
      (∀ g ∈ N, g.card=2 ∧ g ⊆ Finset.univ) ∧
      (∀ g ∈ N, ∀ h ∈ N, g≠h → Disjoint g h) ∧
      (∀ R ∈ H, ∃ g ∈ N, g⊆R) ∧ N.card=s)).card)

def decode (x : List Bool) : List Bool :=
  let a := popHeader x
  let b := popHeader a.2
  outputFor a.1 b.1 (parseFamily a.1 b.2)

theorem decode_spec {n : Nat} (t : Nat) (H : Finset (Finset (Fin n))) (hh : ∀ R ∈ H, R.card=3) :
    decode (header n ++ header t ++ H.toList.flatMap codeRow) =
    (List.range (n/2+1)).flatMap fun s => bits t
      (Nat.card {N : Finset (Finset (Fin n)) // (∀ g ∈ N, g.card=2 ∧ g ⊆ Finset.univ) ∧
      (∀ g ∈ N, ∀ h ∈ N, g≠h → Disjoint g h) ∧
      (∀ R ∈ H, ∃ g ∈ N, g⊆R) ∧ N.card=s}) := by
  simp only [List.append_assoc,decode,pop_header,family_roundtrip H hh,outputFor,
    Nat.card_eq_fintype_card,Fintype.card_subtype]

end PEqualNP.Outside.L_lib_931.Code

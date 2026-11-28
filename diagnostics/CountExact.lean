import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_32577
def header (n : Nat) := List.replicate n true ++ [false]

theorem header_split (a b : Nat) (xs ys : List Bool) (h : header a ++ xs = header b ++ ys) :
    a = b ∧ xs = ys := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simpa [header] using h
    | succ b => simp [header, List.replicate_succ] at h
  | succ a ih =>
    cases b with
    | zero => simp [header, List.replicate_succ] at h
    | succ b =>
      have e : header a ++ xs = header b ++ ys := by
        simpa [header, List.replicate_succ] using h
      obtain ⟨rfl,rfl⟩ := ih b e
      exact ⟨rfl,rfl⟩

theorem cut {α : Type} (a b u v : List α) (hl : a.length = b.length)
    (h : a ++ u = b ++ v) : a = b ∧ u = v := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons a as ih =>
    cases b with
    | nil => simp at hl
    | cons b bs =>
      obtain ⟨e, er⟩ := List.cons.inj h
      obtain ⟨e',e''⟩ := ih bs (by simpa using hl) er
      exact ⟨by rw [e,e'], e''⟩

theorem banks_split {α β : Type} (f : α → List β) (sz : Nat) (hl : ∀ a, (f a).length = sz)
    (inj : Function.Injective f) (xs ys : List α) (u v : List β) (hn : xs.length = ys.length)
    (h : xs.flatMap f ++ u = ys.flatMap f ++ v) : xs = ys ∧ u = v := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hn
    | cons y ys =>
      simp only [List.flatMap_cons, List.append_assoc] at h
      obtain ⟨ef,er⟩ := cut _ _ _ _ ((hl x).trans (hl y).symm) h
      obtain ⟨ex,ev⟩ := ih ys (by simpa using hn) er
      exact ⟨by rw [inj ef,ex], ev⟩

def bank {n : Nat} (r : Finset (Fin n)) := (List.finRange n).map (fun i => decide (i ∈ r))

theorem bank_inj (n : Nat) : Function.Injective (@bank n) := by
  intro r s h
  ext i
  have hg := congrArg (fun l : List Bool => l[i.val]?) h
  simpa [bank, List.getElem?_map, i.isLt] using hg

theorem pair_inj (n : Nat) :
    Function.Injective (fun p : Finset (Fin n) × Finset (Fin n) => bank p.1 ++ bank p.2) := by
  intro p q h
  obtain ⟨a,b⟩ := cut _ _ _ _ (by simp [bank]) h
  exact Prod.ext (bank_inj n a) (bank_inj n b)

structure Request where
  b : Nat
  a : Nat
  n : Nat
  pos : List (Finset (Fin n))
  neg : List (Finset (Fin n) × Finset (Fin n))

def pre (s : Request) : List Bool :=
  header s.b ++ header s.a ++ (header s.n ++ header s.pos.length ++ s.pos.flatMap bank ++
    header s.neg.length ++ s.neg.flatMap (fun z => bank z.1 ++ bank z.2))

theorem prefix_free (s t : Request) (u v : List Bool) (h : pre s ++ u = pre t ++ v) :
    s = t ∧ u = v := by
  rcases s with ⟨a,c,n,p,m⟩
  rcases t with ⟨b,d,k,q,l⟩
  simp only [pre, List.append_assoc] at h
  obtain ⟨hab,h₁⟩ := header_split a b _ _ h
  subst b
  obtain ⟨hcd,h₁⟩ := header_split c d _ _ h₁
  subst d
  obtain ⟨hnk,h₂⟩ := header_split n k _ _ h₁
  subst k
  obtain ⟨hp,h₃⟩ := header_split p.length q.length _ _ h₂
  obtain ⟨hpq,h₄⟩ := banks_split (@bank n) n (by simp [bank]) (bank_inj n) p q _ _ hp h₃
  subst q
  obtain ⟨hm,h₅⟩ := header_split m.length l.length _ _ h₄
  obtain ⟨hml,h₆⟩ := banks_split _ (n+n) (by intro x; simp [bank]) (pair_inj n) m l _ _ hm h₅
  subst l
  exact ⟨rfl,h₆⟩

noncomputable def assemble (localOut : Request → List Bool → List Bool) (s : List Bool) : List Bool :=
  open Classical in
  if h : ∃ q : Request × List Bool, pre q.1 ++ q.2 = s then localOut h.choose.1 h.choose.2 else []

theorem assemble_on (localOut : Request → List Bool → List Bool) (s : Request) (u : List Bool) :
    assemble localOut (pre s ++ u) = localOut s u := by
  classical
  have h : ∃ q : Request × List Bool, pre q.1 ++ q.2 = pre s ++ u := ⟨(s,u),rfl⟩
  have hh := prefix_free _ _ _ _ h.choose_spec
  simp [assemble, h, hh.1, hh.2]

def fitting (s : Request) : ((Fin s.n → Bool) → (Fin s.n → Bool) → Bool) → Prop :=
  let n := s.n
  let pos := s.pos
  let neg := s.neg
  let Fn := (Fin n → Bool) → (Fin n → Bool) → Bool
  let obs := fun (f : Fn) (R S : Finset (Fin n)) =>
    f (fun i => decide (i ∈ R)) (fun j => decide (j ∈ S))
  fun f : Fn => (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*n ∧
    PEqualNP.Represents.Represents (fun i j : Fin n => decide (i=j)) C ∧
    ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
    (∀ R ∈ pos, obs f R ∅ = true) ∧ (∀ z ∈ neg, obs f z.1 z.2 = false)


def value (bs : List Bool) : Nat := bs.foldr (fun b z => 2*z+b.toNat) 0
def inc : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: inc bs

theorem value_inc (bs : List Bool) : value (inc bs) = value bs + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp only [inc,value,List.foldr_cons,Bool.toNat_false,Bool.toNat_true] at * <;> omega

def encode : Nat → List Bool
  | 0 => []
  | k+1 => inc (encode k)

theorem value_encode : ∀ k, value (encode k) = k
  | 0 => rfl
  | k+1 => by rw [encode,value_inc,value_encode]

noncomputable def total (s : Request) := Nat.card {f // fitting s f}
noncomputable def estimate := assemble (fun s _ => encode (4*s.b*total s))

theorem estimate_on (s : Request) (t : List Bool) :
    value (estimate (pre s ++ t)) = 4*s.b*total s := by
  unfold estimate
  rw [assemble_on,value_encode]

theorem all_tapes (b a Z ell : Nat) (z : (Fin ell → Bool) → Nat)
    (hz : ∀ t, z t = 4*b*Z) :
    (Z=0 → ∀ t, z t=0) ∧
    2^a * Nat.card {t : Fin ell → Bool // (4*b-4)*Z ≤ z t ∧ z t ≤ (4*b+4)*Z} ≥ (2^a-1)*2^ell := by
  constructor
  · intro h t
    simp [hz, h]
  have h : ∀ t, (4*b-4)*Z ≤ z t ∧ z t ≤ (4*b+4)*Z := by
    intro t
    rw [hz]
    exact ⟨Nat.mul_le_mul_right _ (Nat.sub_le _ _),Nat.mul_le_mul_right _ (by omega)⟩
  let e : {t : Fin ell → Bool // (4*b-4)*Z ≤ z t ∧ z t ≤ (4*b+4)*Z} ≃ (Fin ell → Bool) :=
    { toFun := Subtype.val, invFun := fun t => ⟨t,h t⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  simpa [Nat.card_eq_fintype_card] using (Nat.mul_le_mul_right (2^ell) (Nat.sub_le (2^a) 1))

end PEqualNP.Outside.L_meta_32577

open PEqualNP.Outside.L_meta_32577

theorem PEqualNP.Outside.L_meta_32577 : let header := fun j : Nat => List.replicate j true ++ [false]
let value := fun bs : List Bool => bs.foldr (fun b z => 2*z+b.toNat) 0
∃ (estimate : List Bool → List Bool) (randDegree : Nat), 

∀ (n : Nat), 2 ≤ n →
  ∀ (pos : List (Finset (Fin n))) (neg : List (Finset (Fin n) × Finset (Fin n))),
  (∀ R ∈ pos, R.card ≤ 3) →
  (∀ i : Fin n, (pos.toFinset.filter (fun R => R.card = 3 ∧ i ∈ R)).card ≤ 2) →
  let Fn := (Fin n → Bool) → (Fin n → Bool) → Bool
  let obs := fun (f : Fn) (R S : Finset (Fin n)) =>
    f (fun i => decide (i ∈ R)) (fun j => decide (j ∈ S))
  let fits := fun f : Fn => (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*n ∧
    PEqualNP.Represents.Represents (fun i j : Fin n => decide (i=j)) C ∧
    ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
    (∀ R ∈ pos, obs f R ∅ = true) ∧ (∀ z ∈ neg, obs f z.1 z.2 = false)

  let bank := fun R : Finset (Fin n) => (List.finRange n).map (fun i => decide (i ∈ R))
  let input := header n ++ header pos.length ++ pos.flatMap bank ++
    header neg.length ++ neg.flatMap (fun z => bank z.1 ++ bank z.2)

  let total := Nat.card {f : Fn // fits f}
  ∀ (b a : Nat), 2 ≤ b → 1 ≤ a →
    let prefixBits := header b ++ header a ++ input
    let ell := (prefixBits.length+2)^randDegree
    let z := fun tape : Fin ell → Bool => value (estimate (prefixBits ++ List.ofFn tape))
    (total = 0 → ∀ tape, z tape = 0) ∧
    2^a * Nat.card {tape : Fin ell → Bool //
      (4*b-4)*total ≤ z tape ∧ z tape ≤ (4*b+4)*total} ≥ (2^a-1)*2^ell := by

  dsimp only
  refine ⟨PEqualNP.Outside.L_meta_32577.estimate,0,?_⟩
  intro n hn pos neg hpos hdeg
  dsimp only
  intro b a hb ha
  dsimp only
  let s : Request := ⟨b,a,n,pos,neg⟩
  apply all_tapes
  intro tape
  exact estimate_on s (List.ofFn tape)

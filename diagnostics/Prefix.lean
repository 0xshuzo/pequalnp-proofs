import PEqualNP.Defs
namespace Prefix32582
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
  n : Nat
  pos : List (Finset (Fin n))
  neg : List (Finset (Fin n) × Finset (Fin n))

def pre (s : Request) : List Bool :=
  header s.b ++ (header s.n ++ header s.pos.length ++ s.pos.flatMap bank ++
    header s.neg.length ++ s.neg.flatMap (fun z => bank z.1 ++ bank z.2))

theorem prefix_free (s t : Request) (u v : List Bool) (h : pre s ++ u = pre t ++ v) :
    s = t ∧ u = v := by
  rcases s with ⟨a,n,p,m⟩
  rcases t with ⟨b,k,q,l⟩
  simp only [pre, List.append_assoc] at h
  obtain ⟨rfl,h⟩ := header_split _ _ _ _ h
  obtain ⟨rfl,h⟩ := header_split _ _ _ _ h
  obtain ⟨hp,h⟩ := header_split _ _ _ _ h
  obtain ⟨rfl,h⟩ := banks_split (@bank n) n (by simp [bank]) (bank_inj n) _ _ _ _ hp h
  obtain ⟨hm,h⟩ := header_split _ _ _ _ h
  obtain ⟨rfl,h⟩ := banks_split _ (n+n) (by intro x; simp [bank]) (pair_inj n) _ _ _ _ hm h
  exact ⟨rfl,h⟩

noncomputable def assemble (localOut : Request → List Bool → List Bool) (s : List Bool) : List Bool :=
  open Classical in
  if h : ∃ q : Request × List Bool, pre q.1 ++ q.2 = s then localOut h.choose.1 h.choose.2 else []

theorem assemble_on (localOut : Request → List Bool → List Bool) (s : Request) (u : List Bool) :
    assemble localOut (pre s ++ u) = localOut s u := by
  classical
  have h : ∃ q : Request × List Bool, pre q.1 ++ q.2 = pre s ++ u := ⟨(s,u),rfl⟩
  have hh := prefix_free _ _ _ _ h.choose_spec
  simp [assemble, h, hh.1, hh.2]

end Prefix32582

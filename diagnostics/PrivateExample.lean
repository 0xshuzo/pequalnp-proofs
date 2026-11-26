import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9806.PrivateExample
abbrev V := Fin 14
def edges : List (V × V) := [(0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
def removed (v : V) := v=7 ∨ v=9 ∨ v=13
def target (x : V → Bool) := ∃ p∈edges,x p.1=true ∧ x p.2=true
def rest (x : V → Bool) := ∃ p∈edges,¬removed p.2 ∧ x p.1=true ∧ x p.2=true
def trigger (x : V → Bool) := x 1=true ∨ rest x
def replacement (x : V → Bool) := x 7=true ∨ x 9=true ∨ x 13=true
theorem hit (x : V → Bool) (hx : target x) : trigger x ∨ replacement x := by
  obtain ⟨p,hp,hl,hr⟩ := hx
  by_cases h : removed p.2
  · right
    rcases h with h|h|h
    · exact Or.inl (h ▸ hr)
    · exact Or.inr (Or.inl (h ▸ hr))
    · exact Or.inr (Or.inr (h ▸ hr))
  · exact Or.inl (Or.inr ⟨p,hp,h,hl,hr⟩)
theorem clean (x : V → Bool) (ht : trigger x) (hr : replacement x) : target x := by
  rcases ht with one|⟨p,hp,_,h1,h2⟩
  · rcases hr with h|h|h
    · exact ⟨(1,7),by decide,one,h⟩
    · exact ⟨(1,9),by decide,one,h⟩
    · exact ⟨(1,13),by decide,one,h⟩
  · exact ⟨p,hp,h1,h2⟩

def row (r : Nat) (v : V) := r.testBit v.val
def testRows : Fin 4 → Nat := ![136,544,8196,127]
def accepted (r : Nat) := edges.any fun p => row r p.1 && row r p.2
def triggered (r : Nat) := row r 1 || edges.any (fun p =>
  decide (p.2≠7 ∧ p.2≠9 ∧ p.2≠13) && row r p.1 && row r p.2)
theorem accept_eq (r : Nat) : accepted r=true ↔ target (row r) := by
  simp [accepted,target,List.any_eq_true]
theorem trigger_eq (r : Nat) : triggered r=true ↔ trigger (row r) := by
  simp [triggered,trigger,rest,removed,List.any_eq_true,and_assoc]
theorem fourRows : ∀i : Fin 4, accepted (testRows i)=decide (i.val<3) ∧
    triggered (testRows i)=decide (i.val=3) := by decide +kernel
abbrev S := BitVec 4
def permitted (a : S) := a.getLsbD 3 || decide ((List.range 3).countP (fun i => a.getLsbD i)≤1)
theorem gate_lower : ∀a b : S, permitted a=true → permitted b=true →
    (a &&& b) ≠ 7 ∧ (a ||| b) ≠ 7 := by decide +kernel
theorem two_gates : ((1 ||| 2 ||| 4 : S)=7) := rfl
def column (v : V) : S := BitVec.ofNat 4 ((List.range 4).foldl
  (fun m i => if row (testRows ⟨i%4,by omega⟩) v then m+2^i else m) 0)
theorem inputs : ∀v : V, permitted (column v)=true := by decide +kernel
theorem split_source : column 7=1 ∧ column 9=2 ∧ column 13=4 := by decide +kernel

theorem required (q : (V → Bool) → Bool)
    (h : ∀x,target x → trigger x ∨ q x=true)
    (c : ∀x,trigger x → q x=true → target x) (i : Fin 4) :
    q (row (testRows i)) = decide (i.val<3) := by
  obtain ⟨f,t⟩ := fourRows i
  by_cases small : i.val<3
  · have ne : i.val≠3 := by omega
    have yes := (accept_eq _).mp (by simpa [small] using f)
    rcases h _ yes with on|qtrue
    · have z := (trigger_eq _).mpr on
      simp [ne] at t
      rw [t] at z
      contradiction
    · simpa [small] using qtrue
  · have eq : i.val=3 := by omega
    simp [small] at f ⊢
    have ht := (trigger_eq _).mp (by simpa [eq] using t)
    cases qq : q (row (testRows i)) with
    | false => rfl
    | true =>
      have hf := (accept_eq _).mpr (c _ ht qq)
      simp [f] at hf

def noNeighbor (a : S) := a.getLsbD 3 || decide (a=0)
theorem unmentioned : ∀v : V, (v≠7 ∧ v≠9 ∧ v≠13) → noNeighbor (column v)=true := by decide +kernel
theorem closed : ∀a b : S, noNeighbor a=true → noNeighbor b=true →
    noNeighbor (a &&& b)=true ∧ noNeighbor (a ||| b)=true := by decide +kernel
theorem allowed : ∀a : S,noNeighbor a=true → permitted a=true := by decide +kernel
end PEqualNP.Outside.L_meta_9806.PrivateExample

import Mathlib

namespace Counter3576

abbrev Vertex (N : ℕ) := (Fin N ⊕ Fin N) ⊕ Fin 2
abbrev Block (d : ℕ) := Bool ⊕ (Fin d × Fin 3)

def L {N : ℕ} (a : Fin N) : Vertex N := .inl (.inl a)
def R {N : ℕ} (b : Fin N) : Vertex N := .inl (.inr b)
def D {N : ℕ} (z : Fin 2) : Vertex N := .inr z

def present {N d : ℕ} (l r : Fin N → Fin d → Fin 3) (bad : Finset (Fin N)) : Vertex N → Block d → Prop
  | .inl (.inl _), .inl s => s=false
  | .inl (.inr _), .inl s => s=true
  | .inr _, .inl _ => True
  | .inl (.inl a), .inr (i,s) => a∈bad ∨ l a i=s
  | .inl (.inr b), .inr (i,s) => r b i=s
  | .inr _, .inr _ => False

def crosses {N : ℕ} (E : Finset (Fin N × Fin N)) : Vertex N → Vertex N → Prop
  | .inl (.inl a), .inl (.inr b) => (a,b)∈E
  | .inl (.inr b), .inl (.inl a) => (a,b)∈E
  | _,_ => False

def polarized {N : ℕ} (E : Finset (Fin N × Fin N)) : SimpleGraph (Vertex N) where
  Adj := crosses E
  symm := by constructor; rintro ((a|b)|d) ((i|j)|e) h <;> exact h
  loopless := by constructor; rintro ((a|b)|d) <;> exact id

def partition {N : ℕ} : Vertex N → Bool
  | .inl (.inr _) => true
  | _ => false

theorem bipartite {N : ℕ} (E : Finset (Fin N × Fin N)) (u v : Vertex N)
    (h : (polarized E).Adj u v) : partition u≠partition v := by
  rcases u with (a|b)|d <;> rcases v with (i|j)|e <;> first | exact False.elim h | decide

theorem nocycle {N : ℕ} (E : Finset (Fin N × Fin N))
    (square : ∀ a a' b b' : Fin N, a≠a' → b≠b' → ¬ ((a,b)∈E ∧ (a,b')∈E ∧ (a',b)∈E ∧ (a',b')∈E))
    (u v w x : Vertex N) (uw : u≠w) (vx : v≠x) :
    ¬ ((polarized E).Adj u v ∧ (polarized E).Adj v w ∧ (polarized E).Adj w x ∧ (polarized E).Adj x u) := by
  rintro ⟨h1,h2,h3,h4⟩
  rcases u with (a|b)|d <;> rcases v with (a'|b')|d' <;> rcases w with (a''|b'')|d'' <;> rcases x with (a'''|b''')|d''' <;>
    first | exact False.elim h1 | exact False.elim h2 | exact False.elim h3 | exact False.elim h4 | skip
  · exact square a a'' b' b''' (fun h => uw (by rw [h])) (fun h => vx (by rw [h])) ⟨h1,h4,h2,h3⟩
  · exact square a' a''' b b'' (fun h => vx (by rw [h])) (fun h => uw (by rw [h])) ⟨h1,h2,h4,h3⟩

theorem represent {N d : ℕ} (i0 : Fin d) (l r : Fin N → Fin d → Fin 3) (bad : Finset (Fin N))
    (E : Finset (Fin N × Fin N)) (spec : ∀ a b, (a,b)∈E ↔ a∉bad ∧ ∀ i, l a i≠r b i)
    (u v : Vertex N) : ¬(polarized E).Adj u v ↔ ∃ j, present l r bad u j ∧ present l r bad v j := by
  have lr (a b : Fin N) : (a,b)∉E ↔ ∃ j, present l r bad (L a) j ∧ present l r bad (R b) j := by
    constructor
    · intro missing
      by_cases isolated : a∈bad
      · exact ⟨.inr (i0,r b i0),Or.inl isolated,rfl⟩
      have equal : ∃ i, l a i=r b i := by
        by_contra! h
        exact missing ((spec a b).mpr ⟨isolated,h⟩)
      obtain ⟨i,h⟩ := equal
      exact ⟨.inr (i,r b i),Or.inr h,rfl⟩
    · rintro ⟨j,h1,h2⟩ edge
      obtain ⟨active,diff⟩ := (spec a b).mp edge
      rcases j with s|⟨i,s⟩
      · exact Bool.noConfusion (h1.symm.trans h2)
      · rcases h1 with isBad|same
        · exact active isBad
        · exact diff i (same.trans h2.symm)
  rcases u with (a|b)|d <;> rcases v with (x|y)|e
  · exact ⟨fun _ => ⟨.inl false,rfl,rfl⟩,fun _ => id⟩
  · exact lr a y
  · exact ⟨fun _ => ⟨.inl false,rfl,True.intro⟩,fun _ => id⟩
  · constructor
    · intro h
      obtain ⟨j,hx,hb⟩ := (lr x b).mp h
      exact ⟨j,hb,hx⟩
    · rintro ⟨j,hb,hx⟩
      exact (lr x b).mpr ⟨j,hx,hb⟩
  · exact ⟨fun _ => ⟨.inl true,rfl,rfl⟩,fun _ => id⟩
  · exact ⟨fun _ => ⟨.inl true,rfl,True.intro⟩,fun _ => id⟩
  · exact ⟨fun _ => ⟨.inl false,True.intro,rfl⟩,fun _ => id⟩
  · exact ⟨fun _ => ⟨.inl true,True.intro,rfl⟩,fun _ => id⟩
  · exact ⟨fun _ => ⟨.inl false,True.intro,True.intro⟩,fun _ => id⟩

theorem vertex_covered {N d : ℕ} (i0 : Fin d) (l r : Fin N → Fin d → Fin 3) (bad : Finset (Fin N))
    (u : Vertex N) : (∃ j, present l r bad u j) ∧ (∃ j, ¬present l r bad u j) := by
  rcases u with (a|b)|z
  · exact ⟨⟨.inl false,rfl⟩,⟨.inl true,by decide⟩⟩
  · exact ⟨⟨.inl true,rfl⟩,⟨.inl false,by decide⟩⟩
  · exact ⟨⟨.inl false,True.intro⟩,⟨.inr (i0,0),id⟩⟩

theorem two_omitted {N d : ℕ} (hN : 2≤N) (l r : Fin N → Fin d → Fin 3) (bad : Finset (Fin N))
    (j : Block d) : ∃ a b : Vertex N, a≠b ∧ ¬present l r bad a j ∧ ¬present l r bad b j := by
  let p : Fin N := ⟨0,by omega⟩
  let q : Fin N := ⟨1,by omega⟩
  have pq : p≠q := by intro h; have e := congrArg Fin.val h; change 0=1 at e;omega
  rcases j with s|i
  · cases s
    · exact ⟨R p,R q,by simpa [R] using pq,by decide,by decide⟩
    · exact ⟨L p,L q,by simpa [L] using pq,by decide,by decide⟩
  · exact ⟨D (N:=N) 0,D (N:=N) 1,by simp [D], id,id⟩

theorem edge_count {N : ℕ} (E : Finset (Fin N × Fin N)) [DecidableRel (polarized E).Adj] :
    E.card ≤ (polarized E).edgeFinset.card := by
  apply Finset.card_le_card_of_injOn (fun p : Fin N × Fin N => s(L p.1,R p.2))
  · rintro ⟨a,b⟩ he
    exact SimpleGraph.mem_edgeFinset.mpr he
  · rintro ⟨a,b⟩ ha ⟨a',b'⟩ hb eq
    rcases Sym2.eq_iff.mp eq with ⟨aa,bb⟩|⟨bad,_⟩
    · simpa [L,R] using Prod.ext (show a=a' by simpa [L] using aa) (show b=b' by simpa [R] using bb)
    · simp [L,R] at bad

end Counter3576

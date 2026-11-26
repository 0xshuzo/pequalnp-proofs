import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9804_guard
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def masks : Array Nat := #[40969, 163878, 327756, 655512, 262448, 524897, 1218, 2437, 4874, 9748, 19496, 38992, 77984, 155968, 311936, 623872, 199168, 398337, 796674, 544772]
def direction (a b : Fin 40) : Bool := decide (20 ≤ b.val) && (masks[b.val-20]!).testBit a.val
def literal : List (Nat × Nat) := [(0, 20), (0, 25), (0, 27), (0, 37), (1, 21), (1, 26), (1, 28), (1, 38), (2, 21), (2, 22), (2, 27), (2, 29), (2, 39), (3, 20), (3, 22), (3, 23), (3, 28), (3, 30), (4, 23), (4, 24), (4, 29), (4, 31), (5, 21), (5, 24), (5, 25), (5, 30), (5, 32), (6, 22), (6, 25), (6, 26), (6, 31), (6, 33), (7, 23), (7, 26), (7, 27), (7, 32), (7, 34), (8, 24), (8, 27), (8, 28), (8, 33), (8, 35), (9, 25), (9, 28), (9, 29), (9, 34), (9, 36), (10, 26), (10, 29), (10, 30), (10, 35), (10, 37), (11, 27), (11, 30), (11, 31), (11, 36), (11, 38), (12, 28), (12, 31), (12, 32), (12, 37), (12, 39), (13, 20), (13, 29), (13, 32), (13, 33), (13, 38), (14, 30), (14, 33), (14, 34), (14, 39), (15, 20), (15, 21), (15, 31), (15, 34), (15, 35), (16, 22), (16, 32), (16, 35), (16, 36), (17, 21), (17, 23), (17, 33), (17, 36), (17, 37), (18, 22), (18, 24), (18, 34), (18, 37), (18, 38), (19, 23), (19, 25), (19, 35), (19, 38), (19, 39)]
theorem posted : ∀ a b : Fin 40, direction a b = true ↔ (a.val,b.val)∈literal := by decide +kernel

def G : SimpleGraph (Fin 40) where
  Adj i j := direction i j = true ∨ direction j i = true
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel G.Adj := fun i j =>
  inferInstanceAs (Decidable (direction i j = true ∨ direction j i = true))
abbrev P (i : Fin 20) : Fin 40 := Fin.castAdd 20 i
abbrev L : Fin 20 → Fin 40 := Fin.natAdd 20
def target (x : Fin 40 → Bool) : Prop :=
  ∃ u v : Fin 40, (u.val,v.val) ∈ literal ∧ x u=true ∧ x v=true
theorem graphTarget (x : Fin 40 → Bool) : target x ↔ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true := by
  constructor
  · rintro ⟨i,j,ij,a,b⟩
    exact ⟨i,j,Or.inl ((posted i j).mpr ij),a,b⟩
  · rintro ⟨i,j,e,hi,hj⟩
    rcases e with e|e
    · exact ⟨i,j,(posted i j).mp e,hi,hj⟩
    · exact ⟨j,i,(posted j i).mp e,hj,hi⟩

abbrev V := Fin 40
def neighborRow : Array (Finset V) := #[{20,25,27,37}, {21,26,28,38}, {21,22,27,29,39}, {20,22,23,28,30}, {23,24,29,31}, {21,24,25,30,32}, {22,25,26,31,33}, {23,26,27,32,34}, {24,27,28,33,35}, {25,28,29,34,36}, {26,29,30,35,37}, {27,30,31,36,38}, {28,31,32,37,39}, {20,29,32,33,38}, {30,33,34,39}, {20,21,31,34,35}, {22,32,35,36}, {21,23,33,36,37}, {22,24,34,37,38}, {23,25,35,38,39}, {0,3,13,15}, {1,2,5,15,17}, {2,3,6,16,18}, {3,4,7,17,19}, {4,5,8,18}, {0,5,6,9,19}, {1,6,7,10}, {0,2,7,8,11}, {1,3,8,9,12}, {2,4,9,10,13}, {3,5,10,11,14}, {4,6,11,12,15}, {5,7,12,13,16}, {6,8,13,14,17}, {7,9,14,15,18}, {8,10,15,16,19}, {9,11,16,17}, {0,10,12,17,18}, {1,11,13,18,19}, {2,12,14,19}]
def N (v : V) := neighborRow[v.val]!
def shore (v : V) : Bool := decide (v.val < 20)
theorem memN : ∀ a b : V, b ∈ N a ↔ G.Adj a b := by decide +kernel
theorem oneBound : ∀ a : V, (N a).card ≤ 5 := by decide +kernel
theorem pairBound : ∀ a b : V, shore a = shore b → (N a ∪ N b).card ≤ 9 := by decide +kernel

theorem fourBound (a b c d : V) : (N a ∪ N b ∪ N c ∪ N d).card ≤ 19 := by
  have go (w x y z : V) (same : shore w=shore x) :
      (N w ∪ N x ∪ N y ∪ N z).card ≤ 19 := by
    have h₁ := Finset.card_union_le (N w ∪ N x) (N y)
    have h₂ := Finset.card_union_le (N w ∪ N x ∪ N y) (N z)
    have h₃ := pairBound w x same
    have h₄ := oneBound y
    have h₅ := oneBound z
    omega
  by_cases ab : shore a=shore b
  · exact go a b c d ab
  by_cases ac : shore a=shore c
  · have e : N a ∪ N b ∪ N c ∪ N d = N a ∪ N c ∪ N b ∪ N d := by ac_rfl
    rw [e]; exact go a c b d ac
  have bc : shore b=shore c := by cases h : shore a <;> cases i : shore b <;> cases j : shore c <;> simp_all
  have e : N a ∪ N b ∪ N c ∪ N d = N b ∪ N c ∪ N a ∪ N d := by ac_rfl
  rw [e]; exact go b c a d bc

def edge (S : Finset V) : Prop := ∃ u ∈ S, ∃ v ∈ S, G.Adj u v
theorem edge_spec (S : Finset V) : edge S ↔ target (fun i => decide (i∈S)) := by
  rw [graphTarget]
  simp only [edge,decide_eq_true_eq]
  constructor
  · rintro ⟨i,hi,j,hj,e⟩; exact ⟨i,j,e,hi,hj⟩
  · rintro ⟨i,j,e,hi,hj⟩; exact ⟨i,hi,j,hj,e⟩

theorem insertion {S : Finset V} {v : V} (ind : ¬edge S) (has : edge (insert v S)) :
    ∃ u∈S, v∈N u := by
  obtain ⟨i,hi,j,hj,adj⟩ := has
  rcases Finset.mem_insert.mp hi with eiv|insideI
  · rcases Finset.mem_insert.mp hj with ejv|insideJ
    · exact (G.loopless.irrefl v (by simpa only [eiv,ejv] using adj)).elim
    · exact ⟨j,insideJ,(memN _ _).2 (SimpleGraph.Adj.symm (show G.Adj v j from eiv ▸ adj))⟩
  · rcases Finset.mem_insert.mp hj with ejv|insideJ
    · exact ⟨i,insideI,(memN _ _).2 (ejv ▸ adj)⟩
    · exact (ind ⟨i,insideI,j,insideJ,adj⟩).elim

theorem opposite_agrees (A B : Finset V → Prop)
    (ma : ∀ {s t}, s⊆t → A s → A t) (mb : ∀ {s t}, s⊆t → B s → B t)
    (correct : ∀s, (A s ∧ B s) ↔ edge s)
    (U : Finset V) (wide : 20≤U.card) (accepts : ∀v∈U,A {v})
    (s : Finset V) (a b c d : V)
    (four : ∀ u∈s, u=a ∨ u=b ∨ u=c ∨ u=d) : B s ↔ edge s := by
  refine ⟨?_,fun e => ((correct s).2 e).2⟩
  intro bs
  by_contra ind
  have sub : U ⊆ N a ∪ N b ∪ N c ∪ N d := by
    intro v hv
    have iA : A (insert v s) := ma (show ({v} : Finset V) ⊆ insert v s from by simp) (accepts v hv)
    have iB : B (insert v s) := mb (Finset.subset_insert _ _) bs
    obtain ⟨u,hu,hN⟩ := insertion ind ((correct _).1 ⟨iA,iB⟩)
    rcases four u hu with rfl|rfl|rfl|rfl <;> simp only [Finset.mem_union] <;> tauto
  have l := Finset.card_le_card sub
  have t := fourBound a b c d
  omega

def pencil : Finset V := {20,24,26,36,39}
def pointGuard (s : Finset V) : Prop := ∃ v∈s, v.val<20
def enlarged (s : Finset V) : Prop := edge s ∨ pencil⊆s
theorem pencilData : pencil.card=5 ∧ ¬edge pencil ∧
    (∀v : V, v.val<20 → ∃w∈pencil,G.Adj v w) := by
  change pencil.card=5 ∧ ¬(∃ u ∈ pencil, ∃ v ∈ pencil, G.Adj u v) ∧ _
  decide +kernel
theorem crossing : ∀ u v : V, G.Adj u v → u.val<20 ∨ v.val<20 := by decide +kernel
theorem sharp (s : Finset V) : pointGuard s ∧ enlarged s ↔ edge s := by
  constructor
  · rintro ⟨⟨u,hu,point⟩,e|extra⟩
    · exact e
    · obtain ⟨v,hv,adj⟩ := pencilData.2.2 u point
      exact ⟨u,hu,v,extra hv,adj⟩
  · intro e
    refine ⟨?_,Or.inl e⟩
    obtain ⟨u,hu,v,hv,adj⟩ := e
    exact (crossing u v adj).elim (fun p=>⟨u,hu,p⟩) (fun p=>⟨v,hv,p⟩)
theorem disagreement : enlarged pencil ∧ ¬edge pencil := ⟨Or.inr (fun _ h=>h),pencilData.2.1⟩
end PEqualNP.Outside.L_meta_9804_guard

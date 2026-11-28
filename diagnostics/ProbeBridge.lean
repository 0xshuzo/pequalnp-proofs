import PEqualNP.Defs

namespace Plane17872Trace

abbrev V := Fin 24
abbrev G := Fin 26
abbrev Wires := ℕ → Finset V
abbrev Homes := G → Finset V
abbrev Dem := Finset (G × ℕ)
abbrev Obligations := Finset (G × V)

def Covers (W : Wires) (D : Dem) (Z : Obligations) :=
  ∀ z ∈ Z, ∃ d ∈ D, d.1 = z.1 ∧ z.2 ∈ W d.2

def Fits (W : Wires) (H : Homes) (D : Dem) (bound : ℕ) :=
  ∀ d ∈ D, d.2 < bound ∧ W d.2 ⊆ H d.1

def Linear (H : Homes) := ∀ (g h : G), g ≠ h →
  ∀ u ∈ H g, u ∈ H h → ∀ v ∈ H g, v ∈ H h → u=v

def Legal (W : Wires) (s : ℕ) := ∀ j<s,
  W (24+j)=∅ ∨ (∃ v, W (24+j)={v}) ∨
  ∃ a<24+j, ∃ b<24+j, W (24+j) = W a ∪ W b

end Plane17872Trace

namespace Plane17872Trace

def graph (a b : Fin 12) : Prop :=
  (9 : Fin 13).succAbove a + (0 : Fin 13).succAbove b ∈ ({0,1,3,9} : Finset (Fin 13))
instance (a b : Fin 12) : Decidable (graph a b) := by unfold graph; infer_instance

abbrev F := {e : Fin 12 × Fin 12 // graph e.1 e.2}
abbrev pt (i : Fin 12) := i.castAdd 12
abbrev ln (i : Fin 12) := i.natAdd 12
def name (i : V) : G := ⟨i.val,by omega⟩
def table : List (Finset V) := [
  {12,14,20},
  {13,19,23},
  {12,18,22,23},
  {17,21,22},
  {16,20,21,23},
  {15,19,20,22},
  {14,18,19,21},
  {13,17,18,20},
  {12,16,17,19},
  {14,15,17,23},
  {13,14,16,22},
  {12,13,15,21},
  {0,2,8,11},
  {1,7,10,11},
  {0,6,9,10},
  {5,9,11},
  {4,8,10},
  {3,7,8,9},
  {2,6,7},
  {1,5,6,8},
  {0,4,5,7},
  {3,4,6,11},
  {2,3,5,10},
  {1,2,4,9},
  {0,1,3},
  {15,16,18}]

def home (g : G) : Finset V := table.getD g.val ∅
def star (i : V) : Finset V := home (name i)

def extra (i : Fin 6) : G × V :=
  ((if i.val<3 then 24 else 25), ([0,1,3,15,16,18] : List V).getD i.val 0)

def flag (b : Bool) (e : F) : G × V :=
  if b then (name (pt e.val.1),ln e.val.2) else (name (ln e.val.2),pt e.val.1)

set_option maxHeartbeats 10000000 in
theorem finite_geometry :
    Fintype.card F=45 ∧
    (∀ (a b : Bool) (e f : F), flag a e=flag b f → e=f) ∧
    (∀ (a : Bool) (e : F) (i : Fin 6), flag a e ≠ extra i) ∧
    (∀ i j : Fin 6, extra i=extra j → i=j) ∧
    (∀ i : Fin 6, (extra i).2 ∈ home (extra i).1) := by decide +kernel

def color (v : V) : Fin 12 := ⟨([0,1,2,3,4,5,6,7,8,9,10,11,8,7,6,5,4,3,2,1,0,11,10,9] : List Nat).getD v.val 0 % 12, Nat.mod_lt _ (by decide)⟩
def diagonal (i : Fin 12) : Fin 12 := ⟨([8,7,6,5,4,3,2,1,0,11,10,9] : List Nat).getD i.val 0 % 12,Nat.mod_lt _ (by decide)⟩

theorem match_geom : ∀ i : Fin 12, graph i (diagonal i) ∧ color (pt i)=i ∧ color (ln (diagonal i))=i := by decide +kernel

def Oriented (W : Wires) {t : Nat} (cen : Fin t → V) (arm : Fin t → Nat) :=
  ∀ e : F, ∃ i : Fin t, ∃ b : Bool, (flag b e).1=name (cen i) ∧ (flag b e).2∈W (arm i)

end Plane17872Trace

namespace Plane17872Trace
open PEqualNP.CircuitLowerBounds

def probe (a b : V) : V → Bool := fun i => decide (i=a ∨ i=b)
def fires (x : V → Bool) := ∃ a b : Fin 12, graph a b ∧ x (pt a)=true ∧ x (ln b)=true
instance (x : V→Bool) : Decidable (fires x) := by unfold fires; infer_instance
def upperP (x : V → Bool) := x 0 || x 1 || x 3
def upperL (x : V → Bool) := x 15 || x 16 || x 18
abbrev read (C : Circuit) (x : V→Bool) (i : Nat) := PEqualNP.BlindGate.wireValue C 24 x i
def Spec (C : Circuit) (q : List (Nat×Nat)) (ma mb : Nat) :=
  ∀ x : V→Bool, ((q.any fun p => read C x p.1 && read C x p.2)=true ↔ fires x) ∧
    (¬fires x → read C x ma = upperP x ∧ read C x mb=upperL x)

set_option maxHeartbeats 6000000 in
theorem sparse_checks :
    (∀ u v : V, fires (probe u v) ↔ v∈star u) ∧
    (∀ u : V, u ∉ star u) ∧
    (∀ u : V, upperP (probe u u)=true ↔ u∈home 24) ∧
    (∀ u : V, upperL (probe u u)=true ↔ u∈home 25) := by decide +kernel

def Agrees (C : Circuit) (W : Wires) := ∀ k<24+C.size, ∀ u v : V,
  read C (probe u v) k=true ↔ u∈W k ∨ v∈W k

theorem sparse_price (clean_price : ∀ {W : Wires} {s t : Nat}, (∀ i : V,W i.val={i}) → Legal W s →
    ∀ (pair : Fin t → Nat × Nat),
    (∀ i, (pair i).1<24+s ∧ (pair i).2<24+s) →
    (∀ i, ∀ u∈W (pair i).1, ∀ v∈W (pair i).2,v∈star u) →
    (∀ e : F, ∃ i : Fin t,
      (pt e.val.1 ∈ W (pair i).1 ∧ ln e.val.2 ∈ W (pair i).2) ∨
      (ln e.val.2 ∈ W (pair i).1 ∧ pt e.val.1 ∈ W (pair i).2)) → ∀ (ma mb : Nat), ma<24+s → mb<24+s → W ma=home 24 → W mb=home 25 → 61 ≤ s+2*t) (C : Circuit) (q : List (Nat×Nat)) (ma mb : Nat) (W : Wires)
    (raw : ∀ i : V,W i.val={i}) (legal : Legal W C.size) (agree : Agrees C W)
    (sp : Spec C q ma mb) (ha : ma<24+C.size) (hb : mb<24+C.size)
    (bounds : ∀ z∈q,z.1 < 24+C.size ∧ z.2 < 24+C.size) : 61≤C.size+2*q.length := by
  classical
  obtain ⟨pairs,irr,markP,markL⟩ := sparse_checks
  have none (u : V) : ¬fires (probe u u) := fun h=>irr u ((pairs u u).mp h)
  have keepP : W ma=home 24 := by
    ext u
    have e := (sp (probe u u)).2 (none u)
    have l := agree ma ha u u
    rw [e.1] at l
    simpa only [← markP, or_self] using l.symm
  have keepL : W mb=home 25 := by
    ext u
    have e := (sp (probe u u)).2 (none u)
    have l := agree mb hb u u
    rw [e.2] at l
    simpa only [← markL, or_self] using l.symm
  let p (i : Fin q.length) := q.get i
  have mem (i : Fin q.length) : p i∈q := List.get_mem _ _
  have bd (i : Fin q.length) := bounds _ (mem i)
  have sound (i : Fin q.length) (u : V) (hu : u∈W (p i).1)
      (v : V) (hv : v∈W (p i).2) : v∈star u := by
    apply (pairs u v).mp
    apply (sp (probe u v)).1.mp
    apply List.any_eq_true.mpr
    refine ⟨p i,mem i,?_⟩
    simp only [Bool.and_eq_true]
    exact ⟨(agree _ (bd i).1 _ _).mpr (Or.inl hu),(agree _ (bd i).2 _ _).mpr (Or.inr hv)⟩
  apply clean_price raw legal p bd sound _ ma mb ha hb keepP keepL
  intro e
  let u := pt e.val.1
  let v := ln e.val.2
  have f : fires (probe u v) := ⟨_,_,e.property,by simp [probe,u],by simp [probe,v]⟩
  obtain ⟨z,hz,ht⟩ := List.any_eq_true.mp ((sp (probe u v)).1.mpr f)
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hz
  change p i=z at hi
  subst z
  simp only [Bool.and_eq_true] at ht
  obtain a|a := (agree _ (bd i).1 _ _).mp ht.1 <;> obtain b|b := (agree _ (bd i).2 _ _).mp ht.2
  · exact (irr u (sound i u a u b)).elim
  · exact ⟨i,Or.inl ⟨a,b⟩⟩
  · exact ⟨i,Or.inr ⟨a,b⟩⟩
  · exact (irr v (sound i v a v b)).elim

end Plane17872Trace

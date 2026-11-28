import PEqualNP.Defs

namespace Research9755.GuardFace
abbrev R := BitVec 10
abbrev W := R → Bool
def raw (i : Fin 10) (x : R) := x.getLsbD i.val
def edges : List (Nat × Nat) := [(0,4),(0,5),(1,2),(1,6),(2,3),(2,7),(3,4),(3,8),(4,9),(5,7),(5,8),(6,8),(6,9),(7,9)]
def cy : List (Nat × Nat) := [(3,4),(4,9),(9,7),(7,5),(5,8),(8,3)]
def adj (E : List (Nat × Nat)) (x : R) := E.any (fun p => x.getLsbD p.1 && x.getLsbD p.2)
def offered : List (List Nat) := [[3,9],[3,5],[9,5],[3,9,5],[4,7],[4,8],[7,8],[4,7,8]]
def join (is : List Nat) (x : R) := is.any (fun i => x.getLsbD i)
def cases' : Array (R × R) := #[(16,17),(4,6),(2,6),(548,556),(385,401),(521,553),(2,66),(276,404),(208,464),(104,616)]
def a (i : Fin 10) := cases'[i.val]!.1
def b (i : Fin 10) := cases'[i.val]!.2
theorem screen : ∀i : Fin 10,adj cy (a i)=false ∧ adj cy (b i)=false ∧
    adj edges (a i)≠adj edges (b i) ∧
    (∀j : Fin 10,j≠i → raw j (a i)=raw j (b i)) ∧
    offered.all (fun s => join s (a i)==join s (b i))=true := by decide +kernel
def flat (w : W) := ∀i : Fin 10,w (a i)=w (b i)
theorem joinFlat (s : List Nat) (hs : s∈offered) : flat (join s) := by
  intro i
  exact beq_iff_eq.mp (List.all_eq_true.mp (screen i).2.2.2.2 s hs)
theorem necessary (S : Finset W) (admissible : ∀w∈S,(∃i,w=raw i) ∨ flat w)
    (correct : ∀ x y : R,adj cy x=false → adj cy y=false →
      (∀w∈S,w x=w y) → adj edges x=adj edges y) : ∀i : Fin 10,raw i∈S := by
  intro i
  by_contra miss
  obtain ⟨az,bz,ne,eq,_⟩ := screen i
  apply ne
  apply correct _ _ az bz
  intro w hw
  rcases admissible w hw with ⟨j,rfl⟩|h
  · apply eq
    rintro rfl
    exact miss hw
  · exact h i
end Research9755.GuardFace

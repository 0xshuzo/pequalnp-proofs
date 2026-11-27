import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9753.Ports
structure Board where
  terms : List Nat
  raw : List Nat
  hints : List Nat
  tests : List (Nat × Nat)
def lit (r h : Nat) : Bool := (r &&& h) != 0
def val (g : Board) (r : Nat) := g.terms.any fun e => (r &&& e)==e
def valid (g : Board) (i x : Nat) :=
  let y := x ||| i
  !val g x && val g y && g.hints.all (fun w => lit x w == lit y w) &&
    g.raw.all (fun j => j==i || lit x j==lit y j)
def test (g : Board) := g.raw.all fun j => g.tests.any fun q => j==q.1 && valid g j q.2
def agrees (hs : List Nat) (a b : Nat) : Prop :=
  ∀ h ∈ hs, lit a h=lit b h

theorem mandatory (g : Board) (checked : test g = true) (chosen : List Nat)
    (allowed : ∀j∈chosen, j∈g.raw)
    (determines : ∀a b, agrees chosen a b → agrees g.hints a b → val g a=val g b) :
    ∀ j ∈ g.raw, j ∈ chosen := by
  intro j hj
  have h := List.all_eq_true.mp checked j hj
  obtain ⟨q,_,hq⟩ := List.any_eq_true.mp h
  have check := (Bool.and_eq_true_iff.mp hq).2
  unfold valid at check
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at check
  by_contra no
  have got := determines q.2 (q.2 ||| j) (by
    intro w hw
    have ne : w≠j := by rintro rfl; exact no hw
    have r := List.all_eq_true.mp check.2 w (allowed w hw)
    simpa [ne] using r) (by
    intro w hw
    exact beq_iff_eq.mp (List.all_eq_true.mp check.1.2 w hw))
  rw [check.1.1.1,check.1.1.2] at got
  contradiction
def b1 : Board := ⟨[129, 257, 1025], [1, 128, 256, 1024], [], [(1, 128), (128, 1), (256, 1), (1024, 1)]⟩
def b3 : Board := ⟨[129, 257, 1025, 130, 514, 8194], [1, 2, 128, 256, 512, 1024, 8192], [768, 1536, 8448, 9216], [(1, 128), (2, 128), (128, 8705), (256, 8705), (512, 1282), (1024, 8705), (8192, 1282)]⟩
def b7 : Board := ⟨[129, 257, 1025, 130, 514, 8194, 260, 4100, 8196], [1, 2, 4, 128, 256, 512, 1024, 4096, 8192], [768, 1536, 4224, 4608, 5120, 5632, 9216], [(1, 128), (2, 128), (4, 256), (128, 12801), (256, 12801), (512, 5378), (1024, 12801), (4096, 1668), (8192, 5378)]⟩
def b11 : Board := ⟨[129, 257, 1025, 130, 514, 8194, 136, 2056, 4104], [1, 2, 8, 128, 256, 512, 1024, 2048, 4096, 8192], [768, 1536, 2304, 2560, 2816, 3072, 4352, 4608, 5120, 5632, 8448, 9216, 10240, 11264, 12288, 12544], [(1, 128), (2, 128), (8, 128), (128, 14849), (256, 14849), (512, 7426), (1024, 14849), (2048, 9992), (4096, 9992), (8192, 7426)]⟩
def b15 : Board := ⟨[129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104], [1, 2, 4, 8, 128, 256, 512, 1024, 2048, 4096, 8192], [768, 1536, 2304, 2560, 2816, 3072, 4608, 5120, 5632, 9216, 10240, 11264], [(1, 128), (2, 128), (4, 256), (8, 128), (128, 14849), (256, 14849), (512, 7426), (1024, 14849), (2048, 9992), (4096, 3716), (8192, 7426)]⟩
def b39 : Board := ⟨[129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 544, 1056, 4128], [1, 2, 4, 32, 128, 256, 512, 1024, 4096, 8192], [768, 4224, 9216], [(1, 128), (2, 128), (4, 256), (32, 512), (128, 12801), (256, 12801), (512, 5378), (1024, 12801), (4096, 1668), (8192, 5378)]⟩
def b31 : Board := ⟨[129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208], [1, 2, 4, 8, 16, 128, 256, 512, 1024, 2048, 4096, 8192], [768, 1536, 2304, 2560, 2816, 4608, 5120, 5632], [(1, 128), (2, 128), (4, 256), (8, 128), (16, 1024), (128, 14849), (256, 14849), (512, 7426), (1024, 14849), (2048, 9992), (4096, 3716), (8192, 7426)]⟩
def b63 : Board := ⟨[129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128], [1, 2, 4, 8, 16, 32, 128, 256, 512, 1024, 2048, 4096, 8192], [768, 2304, 2560, 2816], [(1, 128), (2, 128), (4, 256), (8, 128), (16, 1024), (32, 512), (128, 14849), (256, 14849), (512, 7426), (1024, 14849), (2048, 9992), (4096, 3716), (8192, 7426)]⟩
def boards : List Board := [b1, b3, b7, b11, b15, b39, b31, b63]
theorem boardChecks : boards.all test=true := by decide +kernel
theorem boardPorts {g : Board} (hg : g∈boards) {chosen : List Nat}
    (allowed : ∀j∈chosen, j∈g.raw)
    (determines : ∀a b, agrees chosen a b → agrees g.hints a b → val g a=val g b) :
    ∀j∈g.raw, j∈chosen := mandatory g (List.all_eq_true.mp boardChecks g hg) chosen allowed determines

end PEqualNP.Outside.L_meta_9753.Ports

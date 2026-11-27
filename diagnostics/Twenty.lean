import PEqualNP.Defs
namespace FiveExceptions
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def m245231 : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [3, 11]⟩, ⟨.and, [15, 16]⟩], 17⟩
def a245231 : Circuit := ⟨[⟨.and, [3, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [4, 11]⟩, ⟨.not, [12]⟩], 13⟩
theorem board245231 :
    let A := fun u v : Fin 5 => (245231 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a245231 ∧ a245231.size = 4 ∧ Represents A a245231) ∧ RepSizeAtMost A 8 := by
  dsimp only
  exact ⟨⟨by simp [a245231,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m245231,by simp [m245231,Monotone2],by decide,by decide +kernel⟩⟩
def m507643 : Circuit := ⟨[⟨.or, [6, 7]⟩, ⟨.or, [10, 0]⟩, ⟨.or, [11, 5]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [6, 5]⟩, ⟨.and, [0, 16]⟩, ⟨.or, [17, 13]⟩, ⟨.and, [12, 18]⟩, ⟨.or, [9, 19]⟩, ⟨.or, [15, 20]⟩, ⟨.and, [14, 21]⟩], 22⟩
def a507643 : Circuit := ⟨[⟨.and, [0, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [4, 15]⟩, ⟨.not, [16]⟩], 17⟩
theorem board507643 :
    let A := fun u v : Fin 5 => (507643 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a507643 ∧ a507643.size = 8 ∧ Represents A a507643) ∧ RepSizeAtMost A 13 := by
  dsimp only
  exact ⟨⟨by simp [a507643,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m507643,by simp [m507643,Monotone2],by decide,by decide +kernel⟩⟩
def m515965 : Circuit := ⟨[⟨.or, [0, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [16, 13]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [16, 13]⟩, ⟨.and, [19, 14]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [21, 22]⟩], 23⟩
def a515965 : Circuit := ⟨[⟨.and, [0, 6]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [2, 8]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [4, 16]⟩, ⟨.not, [17]⟩], 18⟩
theorem board515965 :
    let A := fun u v : Fin 5 => (515965 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a515965 ∧ a515965.size = 9 ∧ Represents A a515965) ∧ RepSizeAtMost A 14 := by
  dsimp only
  exact ⟨⟨by simp [a515965,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m515965,by simp [m515965,Monotone2],by decide,by decide +kernel⟩⟩
def m515967 : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [10, 13]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [17, 16]⟩, ⟨.and, [7, 15]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [0, 20]⟩], 21⟩
def a515967 : Circuit := ⟨[⟨.and, [1, 7]⟩, ⟨.and, [2, 8]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [4, 14]⟩, ⟨.not, [15]⟩], 16⟩
theorem board515967 :
    let A := fun u v : Fin 5 => (515967 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a515967 ∧ a515967.size = 7 ∧ Represents A a515967) ∧ RepSizeAtMost A 12 := by
  dsimp only
  exact ⟨⟨by simp [a515967,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m515967,by simp [m515967,Monotone2],by decide,by decide +kernel⟩⟩
def m1293822 : Circuit := ⟨[⟨.and, [4, 5]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [12, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [5, 14]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [6, 18]⟩, ⟨.and, [17, 19]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [11, 21]⟩, ⟨.or, [10, 22]⟩], 23⟩
def a1293822 : Circuit := ⟨[⟨.and, [0, 5]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [0, 5]⟩, ⟨.not, [13]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [10, 16]⟩, ⟨.not, [17]⟩], 18⟩
theorem board1293822 :
    let A := fun u v : Fin 5 => (1293822 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a1293822 ∧ a1293822.size = 9 ∧ Represents A a1293822) ∧ RepSizeAtMost A 14 := by
  dsimp only
  exact ⟨⟨by simp [a1293822,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m1293822,by simp [m1293822,Monotone2],by decide,by decide +kernel⟩⟩
def m1539038 : Circuit := ⟨[⟨.and, [4, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [3, 12]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [7, 15]⟩, ⟨.or, [6, 16]⟩, ⟨.and, [13, 17]⟩, ⟨.or, [10, 18]⟩], 19⟩
def a1539038 : Circuit := ⟨[⟨.and, [4, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [4, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [10, 14]⟩], 15⟩
theorem board1539038 :
    let A := fun u v : Fin 5 => (1539038 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a1539038 ∧ a1539038.size = 6 ∧ Represents A a1539038) ∧ RepSizeAtMost A 10 := by
  dsimp only
  exact ⟨⟨by simp [a1539038,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m1539038,by simp [m1539038,Monotone2],by decide,by decide +kernel⟩⟩
def m1555966 : Circuit := ⟨[⟨.and, [4, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [12, 9]⟩, ⟨.and, [0, 13]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [1, 15]⟩, ⟨.or, [5, 12]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [14, 18]⟩, ⟨.or, [10, 19]⟩], 20⟩
def a1555966 : Circuit := ⟨[⟨.and, [0, 5]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [0, 5]⟩, ⟨.not, [12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [10, 14]⟩, ⟨.not, [15]⟩], 16⟩
theorem board1555966 :
    let A := fun u v : Fin 5 => (1555966 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a1555966 ∧ a1555966.size = 7 ∧ Represents A a1555966) ∧ RepSizeAtMost A 11 := by
  dsimp only
  exact ⟨⟨by simp [a1555966,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m1555966,by simp [m1555966,Monotone2],by decide,by decide +kernel⟩⟩
def m1564542 : Circuit := ⟨[⟨.or, [7, 1]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [16, 5]⟩, ⟨.or, [2, 17]⟩, ⟨.and, [13, 18]⟩, ⟨.and, [11, 10]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [8, 21]⟩, ⟨.and, [17, 22]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [19, 24]⟩], 25⟩
def a1564542 : Circuit := ⟨[⟨.and, [0, 5]⟩, ⟨.not, [5]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [2, 8]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [4, 16]⟩, ⟨.and, [11, 17]⟩, ⟨.or, [10, 18]⟩, ⟨.not, [19]⟩], 20⟩
theorem board1564542 :
    let A := fun u v : Fin 5 => (1564542 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a1564542 ∧ a1564542.size = 11 ∧ Represents A a1564542) ∧ RepSizeAtMost A 16 := by
  dsimp only
  exact ⟨⟨by simp [a1564542,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m1564542,by simp [m1564542,Monotone2],by decide,by decide +kernel⟩⟩
def m1571806 : Circuit := ⟨[⟨.and, [4, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [5, 12]⟩, ⟨.and, [3, 13]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [12, 9]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [14, 18]⟩, ⟨.or, [10, 19]⟩], 20⟩
def a1571806 : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.and, [5, 10]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [4, 13]⟩, ⟨.not, [14]⟩, ⟨.or, [11, 15]⟩], 16⟩
theorem board1571806 :
    let A := fun u v : Fin 5 => (1571806 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a1571806 ∧ a1571806.size = 7 ∧ Represents A a1571806) ∧ RepSizeAtMost A 11 := by
  dsimp only
  exact ⟨⟨by simp [a1571806,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m1571806,by simp [m1571806,Monotone2],by decide,by decide +kernel⟩⟩
def m7598014 : Circuit := ⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [14, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [17, 12]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [17, 12]⟩, ⟨.and, [20, 15]⟩, ⟨.or, [19, 21]⟩], 22⟩
def a7598014 : Circuit := ⟨[⟨.and, [0, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [10, 17]⟩, ⟨.not, [18]⟩], 19⟩
theorem board7598014 :
    let A := fun u v : Fin 5 => (7598014 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a7598014 ∧ a7598014.size = 10 ∧ Represents A a7598014) ∧ RepSizeAtMost A 13 := by
  dsimp only
  exact ⟨⟨by simp [a7598014,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m7598014,by simp [m7598014,Monotone2],by decide,by decide +kernel⟩⟩
def m7720894 : Circuit := ⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [12, 4]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [14, 8]⟩, ⟨.or, [15, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [18, 16]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [2, 9]⟩, ⟨.and, [3, 8]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [20, 21]⟩, ⟨.or, [24, 22]⟩, ⟨.or, [25, 23]⟩], 26⟩
def a7720894 : Circuit := ⟨[⟨.and, [0, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [2, 12]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [3, 14]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [4, 16]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [13, 18]⟩, ⟨.or, [11, 19]⟩, ⟨.or, [10, 20]⟩, ⟨.not, [21]⟩], 22⟩
theorem board7720894 :
    let A := fun u v : Fin 5 => (7720894 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a7720894 ∧ a7720894.size = 13 ∧ Represents A a7720894) ∧ RepSizeAtMost A 17 := by
  dsimp only
  exact ⟨⟨by simp [a7720894,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m7720894,by simp [m7720894,Monotone2],by decide,by decide +kernel⟩⟩
def m7731134 : Circuit := ⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [14, 8]⟩, ⟨.or, [15, 9]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [18, 16]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [3, 8]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [20, 21]⟩, ⟨.or, [23, 22]⟩], 24⟩
def a7731134 : Circuit := ⟨[⟨.and, [0, 5]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [1, 15]⟩, ⟨.and, [13, 16]⟩, ⟨.or, [12, 17]⟩, ⟨.or, [10, 18]⟩, ⟨.not, [19]⟩], 20⟩
theorem board7731134 :
    let A := fun u v : Fin 5 => (7731134 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a7731134 ∧ a7731134.size = 11 ∧ Represents A a7731134) ∧ RepSizeAtMost A 15 := by
  dsimp only
  exact ⟨⟨by simp [a7731134,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m7731134,by simp [m7731134,Monotone2],by decide,by decide +kernel⟩⟩
def m7731167 : Circuit := ⟨[⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [11, 10]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [11, 10]⟩, ⟨.or, [6, 15]⟩, ⟨.and, [14, 13]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [19, 16]⟩, ⟨.and, [5, 18]⟩, ⟨.or, [21, 20]⟩, ⟨.or, [0, 22]⟩, ⟨.or, [17, 23]⟩], 24⟩
def a7731167 : Circuit := ⟨[⟨.and, [1, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [4, 14]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [10, 17]⟩, ⟨.not, [18]⟩], 19⟩
theorem board7731167 :
    let A := fun u v : Fin 5 => (7731167 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a7731167 ∧ a7731167.size = 10 ∧ Represents A a7731167) ∧ RepSizeAtMost A 15 := by
  dsimp only
  exact ⟨⟨by simp [a7731167,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m7731167,by simp [m7731167,Monotone2],by decide,by decide +kernel⟩⟩
def m7860158 : Circuit := ⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [14, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [17, 12]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [17, 12]⟩, ⟨.and, [20, 15]⟩, ⟨.or, [19, 21]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [22, 23]⟩], 24⟩
def a7860158 : Circuit := ⟨[⟨.and, [0, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [9, 14]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [10, 18]⟩, ⟨.not, [19]⟩], 20⟩
theorem board7860158 :
    let A := fun u v : Fin 5 => (7860158 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a7860158 ∧ a7860158.size = 11 ∧ Represents A a7860158) ∧ RepSizeAtMost A 15 := by
  dsimp only
  exact ⟨⟨by simp [a7860158,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m7860158,by simp [m7860158,Monotone2],by decide,by decide +kernel⟩⟩
def m7860159 : Circuit := ⟨[⟨.or, [7, 2]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [3, 14]⟩, ⟨.and, [12, 15]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [3, 11]⟩, ⟨.and, [17, 18]⟩, ⟨.or, [5, 19]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [0, 21]⟩], 22⟩
def a7860159 : Circuit := ⟨[⟨.and, [1, 6]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [9, 13]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [10, 16]⟩, ⟨.not, [17]⟩], 18⟩
theorem board7860159 :
    let A := fun u v : Fin 5 => (7860159 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a7860159 ∧ a7860159.size = 9 ∧ Represents A a7860159) ∧ RepSizeAtMost A 13 := by
  dsimp only
  exact ⟨⟨by simp [a7860159,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m7860159,by simp [m7860159,Monotone2],by decide,by decide +kernel⟩⟩
def m8253374 : Circuit := ⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [14, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [17, 13]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [17, 13]⟩, ⟨.and, [20, 15]⟩, ⟨.or, [19, 21]⟩], 22⟩
def a8253374 : Circuit := ⟨[⟨.and, [0, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [3, 13]⟩, ⟨.or, [2, 14]⟩, ⟨.and, [12, 15]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [10, 17]⟩, ⟨.not, [18]⟩], 19⟩
theorem board8253374 :
    let A := fun u v : Fin 5 => (8253374 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a8253374 ∧ a8253374.size = 10 ∧ Represents A a8253374) ∧ RepSizeAtMost A 13 := by
  dsimp only
  exact ⟨⟨by simp [a8253374,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m8253374,by simp [m8253374,Monotone2],by decide,by decide +kernel⟩⟩
def m8255455 : Circuit := ⟨[⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [13, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [16, 12]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [16, 12]⟩, ⟨.and, [19, 14]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [0, 21]⟩], 22⟩
def a8255455 : Circuit := ⟨[⟨.and, [1, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [4, 13]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [10, 16]⟩, ⟨.not, [17]⟩], 18⟩
theorem board8255455 :
    let A := fun u v : Fin 5 => (8255455 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a8255455 ∧ a8255455.size = 9 ∧ Represents A a8255455) ∧ RepSizeAtMost A 13 := by
  dsimp only
  exact ⟨⟨by simp [a8255455,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m8255455,by simp [m8255455,Monotone2],by decide,by decide +kernel⟩⟩
def m16510910 : Circuit := ⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [16, 12]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [16, 12]⟩, ⟨.and, [19, 13]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [19, 13]⟩, ⟨.and, [22, 14]⟩, ⟨.or, [21, 23]⟩], 24⟩
def a16510910 : Circuit := ⟨[⟨.and, [0, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [2, 7]⟩, ⟨.and, [3, 8]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [10, 17]⟩, ⟨.not, [18]⟩], 19⟩
theorem board16510910 :
    let A := fun u v : Fin 5 => (16510910 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a16510910 ∧ a16510910.size = 10 ∧ Represents A a16510910) ∧ RepSizeAtMost A 15 := by
  dsimp only
  exact ⟨⟨by simp [a16510910,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m16510910,by simp [m16510910,Monotone2],by decide,by decide +kernel⟩⟩
def m16510911 : Circuit := ⟨[⟨.or, [1, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [15, 12]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [15, 12]⟩, ⟨.and, [18, 13]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [21, 20]⟩], 22⟩
def a16510911 : Circuit := ⟨[⟨.and, [1, 6]⟩, ⟨.and, [2, 7]⟩, ⟨.and, [3, 8]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [10, 15]⟩, ⟨.not, [16]⟩], 17⟩
theorem board16510911 :
    let A := fun u v : Fin 5 => (16510911 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a16510911 ∧ a16510911.size = 8 ∧ Represents A a16510911) ∧ RepSizeAtMost A 13 := by
  dsimp only
  exact ⟨⟨by simp [a16510911,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m16510911,by simp [m16510911,Monotone2],by decide,by decide +kernel⟩⟩
def m16510975 : Circuit := ⟨[⟨.or, [2, 7]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [14, 12]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [17, 5]⟩, ⟨.or, [18, 6]⟩, ⟨.or, [19, 16]⟩], 20⟩
def a16510975 : Circuit := ⟨[⟨.and, [2, 7]⟩, ⟨.and, [3, 8]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [10, 13]⟩, ⟨.not, [14]⟩], 15⟩
theorem board16510975 :
    let A := fun u v : Fin 5 => (16510975 : Nat).testBit (5*u.val+v.val)
    (FanInTwo a16510975 ∧ a16510975.size = 6 ∧ Represents A a16510975) ∧ RepSizeAtMost A 11 := by
  dsimp only
  exact ⟨⟨by simp [a16510975,FanInTwo],by decide,by decide +kernel⟩,
    ⟨m16510975,by simp [m16510975,Monotone2],by decide,by decide +kernel⟩⟩
end FiveExceptions

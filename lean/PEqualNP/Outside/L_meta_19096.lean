import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19096

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[
    ⟨.and, [0, 5]⟩,
    ⟨.and, [1, 6]⟩,
    ⟨.and, [2, 7]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [3, 12]⟩,
    ⟨.not, [13]⟩], 14⟩

theorem basis : FanInTwo witness := by
  intro g hg
  simp [witness] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19096

open PEqualNP.Outside.L_meta_19096 in
theorem PEqualNP.Outside.L_meta_19096 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (1981 : ℕ).testBit (4 * u.val + v.val)) C) := by
  exact ⟨witness, basis, by decide +kernel, by decide +kernel⟩

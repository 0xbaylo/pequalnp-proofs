import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

namespace PEqualNP.Outside.L_lib_763_aux
open Module LinearMap
open scoped TensorProduct

theorem range_finrank_tensor
    {F M N P Q : Type*} [Field F]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module F M] [Module F N] [Module F P] [Module F Q]
    [FiniteDimensional F P] [FiniteDimensional F Q]
    (f : M →ₗ[F] P) (g : N →ₗ[F] Q) :
    finrank F (range (TensorProduct.map f g)) =
      finrank F (range f) * finrank F (range g) := by
  let h := TensorProduct.map f.rangeRestrict g.rangeRestrict
  let i := TensorProduct.map (range f).subtype (range g).subtype
  have hs : Function.Surjective h :=
    TensorProduct.map_surjective (LinearMap.surjective_rangeRestrict f) (LinearMap.surjective_rangeRestrict g)
  have hi : Function.Injective i :=
    TensorProduct.map_injective_of_flat_flat _ _ (range f).subtype_injective
      (range g).subtype_injective
  have he : TensorProduct.map f g = i.comp h := by
    ext x y
    rfl
  rw [he, range_comp_of_range_eq_top i (range_eq_top.mpr hs)]
  rw [finrank_range_of_inj hi, Module.finrank_tensorProduct]

open scoped Kronecker

theorem rank_product
    {F m n p q : Type*} [Field F]
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (A : Matrix m n F) (B : Matrix p q F) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  rw [Matrix.rank_eq_finrank_range_toLin (A ⊗ₖ B)
    ((Pi.basisFun F m).tensorProduct (Pi.basisFun F p))
    ((Pi.basisFun F n).tensorProduct (Pi.basisFun F q)),
    Matrix.toLin_kronecker, range_finrank_tensor,
    ← Matrix.rank_eq_finrank_range_toLin A (Pi.basisFun F m) (Pi.basisFun F n),
    ← Matrix.rank_eq_finrank_range_toLin B (Pi.basisFun F p) (Pi.basisFun F q)]

end PEqualNP.Outside.L_lib_763_aux

theorem PEqualNP.Outside.L_lib_763 : (∀ (F : Type) [Field F] (a b c d : ℕ) (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin c) (Fin d) F),
  let K : Matrix (Fin a × Fin c) (Fin b × Fin d) F := fun p q => A p.1 q.1 * B p.2 q.2
  K.rank = A.rank * B.rank) := by
  intro F hF a b c d A B
  exact PEqualNP.Outside.L_lib_763_aux.rank_product A B

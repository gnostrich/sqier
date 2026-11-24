module

public import Mathlib
public import Squier.Main
public import Squier.CriticalPair
public import Squier.S3Aux
@[expose] public section

/-! # The example `S₃`: non-degeneracy, convergence, explicit homotopy basis

The auxiliary results (the homotopy invariant, termination, the classification of the
critical branchings and their resolutions) are in `Squier.S3Aux`. -/

namespace Squier

theorem homotopy_nondegenerate :
    ¬ Homotopic (∅ : Set (Cell s3)) s3StepAAALeft.toPath s3StepAAARight.toPath :=
  S3Aux.homotopy_nondegenerate

theorem s3_convergent : Terminating s3 ∧ Confluent s3 :=
  ⟨S3Aux.terminating,
    (confluent_iff_criticalPairs_joinable s3 S3Aux.terminating).mpr S3Aux.joinable⟩

theorem s3_homotopy_basis : IsHomotopyBasis s3Basis :=
  squier_homotopy_basis s3 S3Aux.terminating s3Basis S3Aux.resolves

end Squier

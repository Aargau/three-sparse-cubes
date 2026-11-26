import SparseCubes.Data.CurvedSum

namespace SparseCubes.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem cell0 : isZero 3 (w1Cell 6 0) = true := by rfl

private theorem cell1 : isZero 3 (w1Cell 6 1) = true := by rfl

theorem w1Row6_checked : isZero 4 (w1Row 6) = true := by
  apply of_slices (N := 2)
  · decide
  · intro j hj
    interval_cases j
    · exact cell0
    · exact cell1

end SparseCubes.Certificate

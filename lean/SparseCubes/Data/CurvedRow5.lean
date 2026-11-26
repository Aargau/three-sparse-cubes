import SparseCubes.Data.CurvedSum

namespace SparseCubes.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem cell0 : isZero 3 (w1Cell 5 0) = true := by rfl

private theorem cell1 : isZero 3 (w1Cell 5 1) = true := by rfl

private theorem cell2 : isZero 3 (w1Cell 5 2) = true := by rfl

private theorem cell3 : isZero 3 (w1Cell 5 3) = true := by rfl

theorem w1Row5_checked : isZero 4 (w1Row 5) = true := by
  apply of_slices (N := 4)
  · decide
  · intro j hj
    interval_cases j
    · exact cell0
    · exact cell1
    · exact cell2
    · exact cell3

end SparseCubes.Certificate

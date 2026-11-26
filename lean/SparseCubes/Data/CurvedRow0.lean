import SparseCubes.Data.CurvedSum

namespace SparseCubes.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem cell0 : isZero 3 (w1Cell 0 0) = true := by rfl

private theorem cell1 : isZero 3 (w1Cell 0 1) = true := by rfl

private theorem cell2 : isZero 3 (w1Cell 0 2) = true := by rfl

private theorem cell3 : isZero 3 (w1Cell 0 3) = true := by rfl

private theorem cell4 : isZero 3 (w1Cell 0 4) = true := by rfl

private theorem cell5 : isZero 3 (w1Cell 0 5) = true := by rfl

private theorem cell6 : isZero 3 (w1Cell 0 6) = true := by rfl

private theorem cell7 : isZero 3 (w1Cell 0 7) = true := by rfl

theorem w1Row0_checked : isZero 4 (w1Row 0) = true := by
  apply of_slices (N := 8)
  · decide
  · intro j hj
    interval_cases j
    · exact cell0
    · exact cell1
    · exact cell2
    · exact cell3
    · exact cell4
    · exact cell5
    · exact cell6
    · exact cell7

end SparseCubes.Certificate

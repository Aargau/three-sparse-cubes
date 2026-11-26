import SparseCubes.Chart1Order4
import SparseCubes.Chart1Order5
import SparseCubes.Chart1Order6
import SparseCubes.Chart1Order7
import SparseCubes.Chart1Order8
import SparseCubes.Chart1Order9

namespace SparseCubes.Chart.Chart1

set_option maxHeartbeats 0
set_option maxRecDepth 100000

variable (b c d e j : ℝ)

theorem rec0 : r0 b c d e j = recRep b c d e j 1 0 := by
  apply rep_ext <;> simp only [r0,recRep,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

theorem rec1 : r1 b c d e j = recRep b c d e j 1 1 := by
  apply rep_ext <;> simp only [r1,recRep,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

theorem rec2 : r2 b c d e j = recRep b c d e j 1 2 := by
  apply rep_ext <;> simp only [r2,recRep,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

theorem rec3 : r3 b c d e j = recRep b c d e j 1 3 := by
  apply rep_ext <;> simp only [r3,recRep,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

theorem base0 : m0 b c d e j = initialRep b c d e j 1 0 := by
  apply rep_ext <;> simp only [m0,initialRep,unit,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

theorem base1 : m1 b c d e j = initialRep b c d e j 1 1 := by
  apply rep_ext <;> simp only [m1,initialRep,unit,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

theorem base2 : m2 b c d e j = initialRep b c d e j 1 2 := by
  apply rep_ext <;> simp only [m2,initialRep,unit,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

theorem base3 : m3 b c d e j = initialRep b c d e j 1 3 := by
  apply rep_ext <;> simp only [m3,initialRep,unit,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

end SparseCubes.Chart.Chart1

import SparseCubes.Chart0Reps

namespace SparseCubes.Chart.Chart0

set_option maxHeartbeats 0
set_option maxRecDepth 100000

variable (b c d e j : ℝ)

theorem rec0 : r0 b c d e j = recRep b c d e j 0 0 := by
  apply rep_ext <;> simp only [r0,recRep,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

theorem rec1 : r1 b c d e j = recRep b c d e j 0 1 := by
  apply rep_ext <;> simp only [r1,recRep,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

theorem rec2 : r2 b c d e j = recRep b c d e j 0 2 := by
  apply rep_ext <;> simp only [r2,recRep,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

theorem rec3 : r3 b c d e j = recRep b c d e j 0 3 := by
  apply rep_ext <;> simp only [r3,recRep,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

theorem base0 : m0 b c d e j = initialRep b c d e j 0 0 := by
  apply rep_ext <;> simp only [m0,initialRep,unit,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

theorem base1 : m1 b c d e j = initialRep b c d e j 0 1 := by
  apply rep_ext <;> simp only [m1,initialRep,unit,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

theorem base2 : m2 b c d e j = initialRep b c d e j 0 2 := by
  apply rep_ext <;> simp only [m2,initialRep,unit,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

theorem base3 : m3 b c d e j = initialRep b c d e j 0 3 := by
  apply rep_ext <;> simp only [m3,initialRep,unit,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

theorem step4 : m4 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j) (m0 b c d e j) := by
  apply rep_ext <;> simp only [linear4,Rep.add,Rep.mul,r0,r1,r2,r3,m0,m1,m2,m3,m4,Certificate.w0G0] <;> ring

theorem step5 : m5 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j) := by
  apply rep_ext <;> simp only [linear4,Rep.add,Rep.mul,r0,r1,r2,r3,m1,m2,m3,m4,m5,Certificate.w0G0,Certificate.w0G1] <;> ring

theorem step6 : m6 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j) := by
  apply rep_ext <;> simp only [linear4,Rep.add,Rep.mul,r0,r1,r2,r3,m2,m3,m4,m5,m6,Certificate.w0G0,Certificate.w0G1,Certificate.w0G2] <;> ring

theorem step7 : m7 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j) := by
  apply rep_ext <;> simp only [linear4,Rep.add,Rep.mul,r0,r1,r2,r3,m3,m4,m5,m6,m7,Certificate.w0G0,Certificate.w0G1,Certificate.w0G2,Certificate.w0G3] <;> ring

theorem step8 : m8 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m7 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j) := by
  apply rep_ext <;> simp only [linear4,Rep.add,Rep.mul,r0,r1,r2,r3,m4,m5,m6,m7,m8,Certificate.w0G0,Certificate.w0G1,Certificate.w0G2,Certificate.w0G3,Certificate.w0G4] <;> ring

theorem step9 : m9 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m8 b c d e j) (m7 b c d e j) (m6 b c d e j) (m5 b c d e j) := by
  apply rep_ext <;> simp only [linear4,Rep.add,Rep.mul,r0,r1,r2,r3,m5,m6,m7,m8,m9,Certificate.w0G1,Certificate.w0G2,Certificate.w0G3,Certificate.w0G4,Certificate.w0G5] <;> ring

end SparseCubes.Chart.Chart0

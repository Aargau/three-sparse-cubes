import SparseCubes.CertificateSlices
import SparseCubes.Data.Chart1

namespace SparseCubes.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def w1Sum : Tower 5 := (add 5 (add 5 (add 5 (add 5 (add 5 (add 5 w1NegH (mul 5 w1C0 w1P0)) (mul 5 w1C1 w1P1)) (mul 5 w1C2 w1P2)) (mul 5 w1C3 w1P3)) (mul 5 w1C4 w1P4)) (mul 5 w1C5 w1P5))

def w1Row (i : Nat) : Tower 4 := slice 4 w1Sum i

def w1Cell (i j : Nat) : Tower 3 := slice 3 (w1Row i) j

end SparseCubes.Certificate

namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Extensions.Math;
    open Microsoft.Quantum.Extensions.Diagnostics;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[], bits : Bool[][]) : Unit {
        let n = Length(qs);
        using (tmp = Qubit[2]) {
            H(tmp[0]);
            H(tmp[1]);
            for (i in 0 .. 3) {
                for (j in 0 .. n - 1) {
                    if (bits[i][j]) {
                        (ControlledOnInt(i, X))(tmp, qs[j]);
                    }
                }
            }
            for (i in 0 .. 3) {
                if ((i &&& 1) != 0) {
                    (ControlledOnBitString(bits[i], X))(qs, tmp[0]);
                }
                if ((i &&& 2) != 0) {
                    (ControlledOnBitString(bits[i], X))(qs, tmp[1]);
                }
            }
        }
    }
}
// https://docs.microsoft.com/en-us/qsharp/api/prelude/microsoft.quantum.primitive?view=qsharp-preview
// https://github.com/Microsoft/QuantumKatas/blob/master/quickref/qsharp-quick-reference.pdf
// https://codeforces.com/contest/1115/standings

namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Set (desired: Result, q1: Qubit) : () {
        body {
            let current = M(q1);
            if (desired != current) { X(q1); }
        }
    }

    operation Solve (qs : Qubit[], bits : Bool[][]) : Unit {
        let n = Length(qs);
        using (Q = Qubit[2]) {
            H(Q[0]); H(Q[1]);
            
            // change stuff
            X(Q[0]); X(Q[1]);
            for (i in 0..n-1) {
                if (bits[0][i]) {
                    Controlled X(Q,qs[i]);
                }
            }
            X(Q[0]); X(Q[1]);
            
            X(Q[1]);
            for (i in 0..n-1) {
                if (bits[1][i]) {
                    Controlled X(Q,qs[i]);
                }
            }
            X(Q[1]);
            
            X(Q[0]);
            for (i in 0..n-1) {
                if (bits[2][i]) {
                    Controlled X(Q,qs[i]);
                }
            }
            X(Q[0]);
            
            for (i in 0..n-1) {
                if (bits[3][i]) {
                    Controlled X(Q,qs[i]);
                }
            }
            
            for (i in 0..n-1) {
                if (!bits[1][i]) {
                    X(qs[i]);
                }
            }
            Controlled X(qs,Q[0]);
            for (i in 0..n-1) {
                if (!bits[1][i]) {
                    X(qs[i]);
                }
            }
            
            for (i in 0..n-1) {
                if (!bits[2][i]) {
                    X(qs[i]);
                }
            }
            Controlled X(qs,Q[1]);
            for (i in 0..n-1) {
                if (!bits[2][i]) {
                    X(qs[i]);
                }
            }
            
            for (i in 0..n-1) {
                if (!bits[3][i]) {
                    X(qs[i]);
                }
            }
            Controlled X(qs,Q[0]);
            Controlled X(qs,Q[1]);
            for (i in 0..n-1) {
                if (!bits[3][i]) {
                    X(qs[i]);
                }
            }
            
            // clear Q
        }
        // your code here
    }
    
    // ------------- Operation which is called from C# -------------------
    // operation RunQsharp () : Bool {
    //     body {
    //         for (j in 0..4) {
    //             using (Q = Qubit()) {
    //                 // X(Q);
    //                 // CNOT(Q,Q);
    //             }
    //         }
    //         return false;
    //     }
    // }
}
// https://docs.microsoft.com/en-us/qsharp/api/prelude/microsoft.quantum.primitive?view=qsharp-preview
// https://github.com/Microsoft/QuantumKatas/blob/master/quickref/qsharp-quick-reference.pdf
// https://codeforces.com/contest/1115/standings

namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    // operation Set (desired: Result, q1: Qubit) : () {
    //     body {
    //         let current = M(q1);
    //         if (desired != current) { X(q1); }
    //     }
    // }

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
            let n = Length(x);
            for (i in 0..n-1) {
                if (i % 2 == 0) {
                    X(x[i]);
                }
            }
            Controlled X(x,y);
            for (i in 0..n-1) {
                if (i % 2 == 0) {
                    X(x[i]);
                }
            }
            for (i in 0..n-1) {
                if (i % 2 == 1) {
                    X(x[i]);
                }
            }
            Controlled X(x,y);
            for (i in 0..n-1) {
                if (i % 2 == 1) {
                    X(x[i]);
                }
            }
            // your code here
        }
        adjoint auto;
    }
    
    // ------------- Operation which is called from C# -------------------
    // operation RunQsharp () : Bool {
    //     body {
    //         for (j in 0..4) {
    //             using (Q = Qubit[4]) {
                
    //             }
    //         }
    //         return false;
    //     }
    // }
}
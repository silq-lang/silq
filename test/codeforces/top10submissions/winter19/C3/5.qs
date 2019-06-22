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
    
    operation mod (Q: Qubit[], x: Qubit) : Unit {
        body (...) {
            Controlled X([Q[0],x],Q[1]);
            X(Q[1]);
            Controlled X([Q[1],x],Q[0]);
            X(Q[1]);
        }
        adjoint auto;
    }

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
            let N = Length(x);
            using (Q = Qubit[2]) {
                for (i in 0..N-1) {
                    mod(Q,x[i]);
                }
                X(Q[0]); X(Q[1]);
                Controlled X(Q,y);
                X(Q[0]); X(Q[1]);
                for (i in 0..N-1) {
                    mod(Q,x[i]);
                }
                for (i in 0..N-1) {
                    mod(Q,x[i]);
                }
            }
        }
        adjoint auto;
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
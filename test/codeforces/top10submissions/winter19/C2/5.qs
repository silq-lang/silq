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

    operation mod(tmp: Qubit, x: Qubit[], i: Int) : Unit {
        body (...) {
            for (j in i..Length(x)-1) {
                CNOT(x[j%i],x[j]);
                X(x[j]);
            }
            Controlled X(x[i..Length(x)-1],tmp);
            for (j in i..Length(x)-1) {
                CNOT(x[j%i],x[j]);
                X(x[j]);
            }
        }
        adjoint auto;
    }
    
    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
            let n = Length(x);
            using (tmp = Qubit[n-1]) {
                for (i in 1..n-1) {
                    X(tmp[i-1]); // 0 if not ok
                    mod(tmp[i-1],x,i);
                }
                X(y); Controlled X(tmp,y);
                for (i in 1..n-1) {
                    X(tmp[i-1]);
                    mod(tmp[i-1],x,i);
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
    //             using (Q = Qubit()) {
    //                 // X(Q);
    //                 // CNOT(Q,Q);
    //             }
    //         }
    //         return false;
    //     }
    // }
}
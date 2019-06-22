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

    operation Solve (qs : Qubit[]) : Unit {
        let N = Length(qs);
        
        for (i in 1..N-1) {
            CNOT(qs[0],qs[i]);
        }
        H(qs[0]);
        for (i in 1..N-1) {
            CNOT(qs[0],qs[i]);
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
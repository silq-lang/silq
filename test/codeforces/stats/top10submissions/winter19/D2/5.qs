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
        // your code here
        let N = Length(qs);
        for (i in 0..N-1) {
            for (j in i+1..N-1) {
                X(qs[j]);
            }
            for (j in 0..i-1) {
                Controlled H(qs[i..N-1],qs[j]);
            }
            for (j in i+1..N-1) {
                X(qs[j]);
            }
        }
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
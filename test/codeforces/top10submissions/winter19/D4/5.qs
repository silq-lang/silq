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
        X(qs[N-1]);
        for (i in 0..N-2) { CNOT(qs[N-1],qs[i]); }
        X(qs[N-1]);
        
        using (tmp = Qubit[N]) {
            for (i in 0..N-1) {
                for (j in 0..i-1) { X(qs[j]); }
                if (i == N-1) {
                    Controlled X(qs[0..i-1],tmp[i]);
                } else {
                    Controlled X(qs[0..i],tmp[i]);
                }
                for (j in 0..i-1) { X(qs[j]); }
            }
            for (i in 0..N-1) {
                for (j in 0..i) {
                    CNOT(tmp[i],qs[j]);
                }
            }
            for (i in 0..N-1) {
                if (i == N-1) {
                    Controlled X(qs[0..i-1],tmp[i]);
                } else {
                    X(qs[i]);
                    Controlled X(qs[0..i],tmp[i]);
                    X(qs[i]);
                }
            }
        }
        H(qs[N-1]);
        for (i in 0..N-2) {
            CNOT(qs[N-1],qs[i]);
        }
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
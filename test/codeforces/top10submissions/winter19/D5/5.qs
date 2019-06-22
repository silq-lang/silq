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
        using (flag = Qubit()) {
            X(qs[0]); X(qs[2]); Controlled X(qs,flag); X(qs[0]); X(qs[2]); 
            X(qs[0]); X(qs[1]); Controlled X(qs,flag); X(qs[0]); X(qs[1]);
            CNOT(flag,qs[1]); CNOT(flag,qs[2]);
            X(qs[0]); X(qs[2]); Controlled X(qs,flag); X(qs[0]); X(qs[2]); 
            X(qs[0]); X(qs[1]); Controlled X(qs,flag); X(qs[0]); X(qs[1]);
        }
        using (flag = Qubit()) {
            X(flag); CNOT(qs[1],flag); CNOT(qs[2],flag);
            CCNOT(flag,qs[1],qs[2]);
            Controlled H([flag],qs[1]);
            CCNOT(flag,qs[1],qs[2]);
            X(flag); CNOT(qs[1],flag); CNOT(qs[2],flag);
            // ?00
            // ?11
        }
        // 0,1 or 6,7 -> try to flip
        H(qs[0]);
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
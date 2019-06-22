// https://docs.microsoft.com/en-us/qsharp/api/prelude/microsoft.quantum.primitive?view=qsharp-preview
// https://github.com/Microsoft/QuantumKatas/blob/master/quickref/qsharp-quick-reference.pdf
// https://codeforces.com/contest/1115/standings

namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Extensions.Convert;

    // operation Set (desired: Result, q1: Qubit) : () {
    //     body {
    //         let current = M(q1);
    //         if (desired != current) { X(q1); }
    //     }
    // }
    operation shiftUp(qs: Qubit[]) : Unit {
        let N = Length(qs);
        using (tmp = Qubit[N+1]) {
            for (i in 0..N) {
                if (i == N) {
                    Controlled X(qs[0..i-1],tmp[i]);
                } else {
                    X(qs[i]); Controlled X(qs[0..i],tmp[i]); X(qs[i]);
                }
            }
            for (i in 0..N) {
                mutable zz = i;
                if (i == N) { set zz = i-1; }
                for (j in 0..zz) {
                    CNOT(tmp[i],qs[j]);
                }
            }
            for (i in 0..N) {
                mutable zz = i;
                for (j in 0..i-1) { X(qs[j]); }
                if (i == N) { set zz = i-1; }
                Controlled X(qs[0..zz],tmp[i]);
                for (j in 0..i-1) { X(qs[j]); }
            }
        }
    }
    operation Solve (qs : Qubit[]) : Unit {
        let N = Length(qs);
        mutable num = 2; for (i in 1..N-1) { set num = num*2; }
        set num = num-2;
        shiftUp(qs); shiftUp(qs); 
        // Message("WHAT "+ToStringI(num));
        for (i in 0..num) {
            for (j in 1..N-1) { X(qs[j]); }
            // Controlled H(qs[1..N-1],qs[0]);
            Controlled Ry (qs[1..N-1],(1.5,qs[0]));
            // Controlled (qs[1..N-1],qs[0]);
            for (j in 1..N-1) { X(qs[j]); }
            if (i != num) {
                shiftUp(qs);
            }
        }
    }

    // operation get(Q: Qubit) : String {
    //     let x = M(Q);
    //     if (x == Zero) { return "Zero"; }
    //     return "One";
    // }
    
    
    
    // // ------------- Operation which is called from C# -------------------
    // operation RunQsharp () : Bool {
    //     body {
    //         for (i in 0..20) {
    //             using (Q = Qubit[3]) {
    //                 // X(Q[2]);
    //                 // Solve(Q);
    //                 // Message("HUH "+get(Q[0])+" "+get(Q[1])+" "+get(Q[2])); // +" "+get(Q[2])
    //                 // ResetAll(Q);
    //             }
    //         }
    //         return false;
    //     }
    // }
}
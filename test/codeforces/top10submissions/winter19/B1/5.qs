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
    
    // operation tri(a: Qubit, b: Qubit): () {
    //     body {
    //         (Controlled H)([a],b);
    //         CNOT(b,a);
    //     }
    // }
    
    // operation get(Q: Qubit) : String {
    //     let x = M(Q);
    //     if (x == Zero) { return "Zero"; }
    //     return "One";
    // }
    
    operation Solve (qs : Qubit[]) : Int {
        let w = 2.0*3.14159265358979/3.0; 
        R1(-w,qs[1]); R1(-2.0*w,qs[2]);
        CNOT(qs[1],qs[0]); CNOT(qs[2],qs[0]);
        X(qs[2]); Controlled H([qs[2]],qs[1]); X(qs[2]);
        // printQubit(qs[0]);
        // printQubit(qs[1]);
        // printQubit(qs[2]);
        Ry(-1.23095941734,qs[2]);
        // Message(get(qs[0])+" "+get(qs[1])+" "+get(qs[2]));
        if (M(qs[1]) == Zero && M(qs[2]) == Zero) {
            return 0;
        }
        return 1;
    }
    
    
    // ------------- Operation which is called from C# -------------------
    // operation RunQsharp () : Bool {
    //     body {
    //         let w = 2.0*3.14159265358979/3.0; 
    //         for (i in 0..20) {
    //             using (Q = Qubit[4]) {
    //                 mutable ok = false;
    //                 repeat {
    //                     ResetAll(Q);
    //                     Set(One,Q[0]);
    //                     tri(Q[0],Q[2]);
    //                     tri(Q[0],Q[1]);
    //                     tri(Q[2],Q[3]);
    //                     if (M(Q[3]) == Zero) {
    //                         set ok = true;
    //                     }
    //                 } until (ok) fixup { }
    //                 // Message(get(Q[0])+" "+get(Q[1])+" "+get(Q[2]));
    //                 // R1(w,Q[1]); R1(2.0*w,Q[2]);
    //                 let z = Solve(Q[0..2]);
    //                 // Message(ToStringI(z));
    //                 ResetAll(Q);
    //             }
    //         }
    //         return false;
    //     }
    // }
}
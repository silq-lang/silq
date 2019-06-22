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
    
    operation hmid(qs: Qubit[]) : Unit {
        CNOT(qs[0],qs[1]);
        Controlled X([qs[1]],qs[0]);
        Controlled Z([qs[1]],qs[0]);
        Controlled H([qs[1]],qs[0]);
        CNOT(qs[0],qs[1]);
    }

    operation mod(qs: Qubit[]) : Unit {
        hmid(qs); 
        X(qs[0]);
        Controlled S([qs[0]],qs[1]);
        X(qs[0]);

        X(qs[1]);
        Controlled Ry([qs[1]],(-1.910633236249,qs[0]));
        Controlled Z([qs[1]],qs[0]);
        X(qs[1]);
        Z(qs[1]);

        hmid(qs);

    }
    
    operation Solve (q : Qubit) : Int {
        // your code here
        mutable ans = -1;
        using (Q = Qubit()) {
            CNOT(q,Q); CNOT(Q,q);
            Z(Q);
            mod([q,Q]);
            
            if (M(q) == Zero && M(Q) == Zero) {
                set ans = 0;
            }
            if (M(q) == One && M(Q) == Zero) {
                set ans = 2;
            }
            if (M(q) == Zero && M(Q) == One) {
                set ans = 1;
            }
            Reset(Q);
        }
        return ans;
    }
    
    
    // ------------- Operation which is called from C# -------------------
    operation RunQsharp () : Bool {
        body {
            for (i in 0..20) {
                using (Q = Qubit()) {
                    H(Q);
                    Message(ToStringI(Solve(Q)));
                    Reset(Q);
                }
            }
            return false;
        }
    }
}
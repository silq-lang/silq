namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Set (desired: Result, q1: Qubit) : ()
    {
        body
        {
            let current = M(q1);
            if (desired != current) { X(q1); }
        }
    }
    
    operation tri(a: Qubit, b: Qubit): () 
    {
        body 
        {
            (Controlled H)([a],b);
            CNOT(b,a);
        }
    }

    operation Solve (qs : Qubit[]) : ()
    {
        body
        {
            for (i in 0..Length(qs)-1) {
                Set(Zero,qs[i]);
            }
            Set(One,qs[0]);
            
            if (Length(qs) >= 2) {
                for (i in 0..0) {
                    tri(qs[i],qs[i+1]);
                }
            }
            if (Length(qs) >= 4) {
                for (i in 0..1) {
                    tri(qs[i],qs[i+2]);
                }
            }
            if (Length(qs) >= 8) {
                for (i in 0..3) {
                    tri(qs[i],qs[i+4]);
                }
            }
            if (Length(qs) >= 16) {
                for (i in 0..7) {
                    tri(qs[i],qs[i+8]);
                }
            }
        }
    }
    
    // ------------- Operation which is called from C# -------------------
    // operation RunQsharp () : Bool
    // {
    //     body
    //     {
    //         for (j in 0..4) {
    //             using (Q = Qubit[4]) {
    //                 Solve(Q);
                    
    //                 for (i in 0..3) {
    //                     if (M(Q[i]) == Zero) {
    //                         Message("0");
    //                     } else {
    //                         Message("1");
    //                     }
    //                 }
    //                 Message("Z");
    //                 for (i in 0..3) {
    //                     Set(Zero,Q[i]);
    //                 }
    //             }
    //         }
    //         return false;
    //     }
    // }
}
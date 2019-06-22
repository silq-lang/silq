namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    // operation Set (desired: Result, q1: Qubit) : ()
    // {
    //     body
    //     {
    //         let current = M(q1);
    //         if (desired != current) { X(q1); }
    //     }
    // }
    
    operation Solve (q : Qubit) : Int
    {
        body
        {
            if (RandomInt(2) == 0) {
                if (M(q) == One) {
                    return 1;
                } else {
                    return -1;
                }

            } else {
                Ry(3.1415926535/2.0,q);
                if (M(q) == Zero) {
                    return 0;
                } else {
                    return -1;
                }
            }
        }
    }
    
    // ------------- Operation which is called from C# -------------------
    // operation RunQsharp () : Bool
    // {
    //     body
    //     {
    //         for (i in 0..99) {
    //             using (res = Qubit[1]) {
    //                 Set(Zero,res[0]);
    //                 H(res[0]);
    //                 mutable t = Solve(res[0]);
    //                 if (t == 0) {
    //                     Message("0");
    //                 }
    //                 if (t == 1) {
    //                     Message("1");
    //                 }
    //                 if (t == -1) {
    //                     Message("-1");
    //                 }
    //                 Set(Zero,res[0]);
    //             }
    //         }
    //         return true;
    //     }
    // }
}
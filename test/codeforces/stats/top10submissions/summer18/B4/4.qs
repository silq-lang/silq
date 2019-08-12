namespace Solution
{
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Primitive;

    // operation Set (desired: Result, q1: Qubit) : ()
    // {
    //     body
    //     {
    //         let current = M(q1);
    //         if (desired != current) { X(q1); }
    //     }
    // }

    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
            H(qs[0]);
            CNOT(qs[0],qs[1]);
            if (M(qs[1]) == One) {
                // 0: 11-01
                // 2: -11-01
                H(qs[0]);
                if (M(qs[0]) == One) {
                    return 0;
                } else {
                    return 2;
                }
            } else {
                // 1: -00+10
                // 3: -00-10
                H(qs[0]);
                
                if (M(qs[0]) == One) {
                    return 1;
                } else {
                    return 3;
                }
            }
        }
    }
}
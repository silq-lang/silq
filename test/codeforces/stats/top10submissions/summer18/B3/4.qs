namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
            H(qs[0]); H(qs[1]);

            if (M(qs[0]) == Zero) {
                if (M(qs[1]) == Zero) {
                    return 0;
                } else {
                    return 1;
                }
            } else {
                if (M(qs[1]) == Zero) {
                    return 2;
                } else {
                    return 3;
                }

            }
        }
    }
}
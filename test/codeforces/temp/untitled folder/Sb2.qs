namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
            // measure all qubits; if there is exactly one One, it’s W state,
            // if there are no Ones or all are Ones, it’s GHZ
            mutable countOnes = 0;
            for (i in 0..Length(qs)-1) {
                if (M(qs[i]) == One) {
                    set countOnes = countOnes + 1;
                }
            }
            if (countOnes == 1) {
                return 1;
            }
            return 0;
        }
    }
}
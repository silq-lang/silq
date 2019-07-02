namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    function FindFirstDiff (bits0 : Bool[], bits1 : Bool[]) : Int
    {
        mutable firstDiff = -1;
        for (i in 0 .. Length(bits1)-1) {
            if (bits1[i] != bits0[i] && firstDiff == -1) {
                set firstDiff = i;
            } 
        }
        return firstDiff;
    }

    operation Solve (qs : Qubit[], bits0 : Bool[], bits1 : Bool[]) : ()
    {
        body
        {
            // find the index of the first bit at which the bitstrings are different
            let firstDiff = FindFirstDiff(bits0, bits1);
            H(qs[firstDiff]);

            // iterate through the bitstrings again setting the final state of qubits
            for (i in 0 .. Length(qs)-1) {
                if (bits0[i] == bits1[i]) {
                    // if two bits are the same apply X or nothing
                    if (bits0[i]) {
                        X(qs[i]);
                    }
                } else {
                    // if two bits are different, set their difference using CNOT
                    if (i > firstDiff) {
                        CNOT(qs[firstDiff], qs[i]);
                        if (bits0[i] != bits0[firstDiff]) {
                            X(qs[i]);
                        } 
                    }
                }
            }
        }
    }
}
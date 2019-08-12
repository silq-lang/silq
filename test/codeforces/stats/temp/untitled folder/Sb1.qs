namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
            // measure all qubits
            // if there is at least one One, it’s W state, if there are no Ones, it’s |0...0>
            // (and you can return as soon as get the first One)
            for (i in 0..Length(qs)-1) {
                if (M(qs[i]) == One) {
                    return 1;
                } 
            }
            return 0; 
        }
    }
}
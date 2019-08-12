namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    operation Solve (qs : Qubit[], bits : Bool[]) : ()
    {
        body
        {
            // Hadamard first qubit
            H(qs[0]);

            // iterate through the bitstring and CNOT to qubits corresponding to true bits
            for (i in 1..Length(qs)-1) {
                if (bits[i]) {
                    CNOT(qs[0], qs[i]);
                } 
            }
        } 
    }
}
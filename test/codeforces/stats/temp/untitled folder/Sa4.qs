namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : ()
    {
        body
        {
            let N = Length(qs);
            if (N == 1) {
                // base of recursion: |1>
                X(qs[0]);
            } else {
                let K = N / 2;
                // create W state on the first K qubits
                Solve(qs[0..K-1]);

                // the next K qubits are in |0...0> state
                // allocate ancilla in |+> state
                using (anc = Qubit[1]) {
                    let here = anc[0];
                    H(here);
                    for (i in 0..K-1) {
                        (Controlled SWAP)([here], (qs[i], qs[i+K]));
                    }
                    // unentangle here from the rest of the qubits
                    for (i in K..N-1) {
                        CNOT(qs[i], here);
                    } 
                }
            }
        }
        adjoint auto;
    }
}

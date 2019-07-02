namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    operation Solve (N : Int, Uf : ((Qubit[], Qubit) => ())) : Int[]
    {
        body
        {
            mutable r = new Int[N];

            // allocate N+1 qubits
            using (qs = Qubit[N+1]) {
                // split allocated qubits into input register and answer register
                let x = qs[0..N-1];
                let y = qs[N];

                // prepare qubits in the right state
                ApplyToEach(H, x);
                X(y);
                H(y);

                // apply oracle
                Uf(x, y);

                // apply Hadamard to each qubit of the input register
                ApplyToEach(H, x);

                // measure all qubits of the input register;
                // the result of each measurement is converted to a Bool
                for (i in 0..N-1) {
                    if (M(x[i]) != Zero) {
                        set r[i] = 1;
                    } 
                }

                // before releasing the qubits make sure they are all in |0> state
                ResetAll(qs);
            }
            return r; 
        }
    }
}
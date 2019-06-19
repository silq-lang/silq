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

                // apply oracle to qubits in all 0 state
                Uf(x, y);

                // remove the N from the expression
                if (N % 2 == 1) {
                    X(y);
                }

                // now y = sum of r

                // measure the output register
                let m = M(y);
                if (m == One) {
                    // adjust parity of bit vector r
                    set r[0] = 1; 
                }

                // before releasing the qubits make sure they are all in |0> state
                ResetAll(qs);
            }
            return r; 
        }
    }
}
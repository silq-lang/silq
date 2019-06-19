namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (N : Int, Uf : ((Qubit[], Qubit) => ())) : Int[]
    {
        body
        {
            mutable r = new Int[N];
            for (i in 0..N-1) {
                set r[i] = 0;
            }
            using (register = Qubit[N + 1]) {
                ApplyToEach(X, register[0..N-1]);
                Uf(register[0..N-1], register[N]);
                if (M(register[N]) == One) {
                    set r[0] = 1;
                }
                ResetAll(register);
            }
            return r;
        }
    }
}
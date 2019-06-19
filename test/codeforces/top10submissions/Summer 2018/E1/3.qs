namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (N : Int, Uf : ((Qubit[], Qubit) => ())) : Int[]
    {
        body
        {
            mutable r = new Int[N];
            using (qs = Qubit[N + 1]) {
                let xs = qs[0..N-1];
                let y = qs[N];
                X(y);
                for (i in 0..N-1) {
                    H(xs[i]);
                }
                H(y);
                Uf(xs, y);
                for (i in 0..N-1) {
                    H(xs[i]);
                }

                for (i in 0..N-1) {
                    if (M(xs[i]) == One) {
                        set r[i] = 1;
                        X(xs[i]);
                    }
                    else {
                        set r[i] = 0;
                    }
                }
                if (M(y) == One) {
                    X(y);
                }
            }
            return r;
        }
    }
}
namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (N : Int, Uf : ((Qubit[], Qubit) => ())) : Int[]
    {
        body
        {
            mutable b = new Int[N];
            using (qs = Qubit[N+1])
            {
                    for (j in 0..N)
                    {
                        let re = M(qs[j]);
                        if (re == One)
                        {
                            X(qs[j]);
                        }
                        H(qs[j]);
                    }
                    H(qs[N]); 
                    X(qs[N]); 
                    H(qs[N]);
                    Uf(qs[0..N-1], qs[N]);
                    for (j in 0..N-1)
                    {
                        H(qs[j]);
                        let re1 = M(qs[j]);
                        if (re1 == One)
                        {
                            set b[j] = 1;
                        }
                        else
                        {
                            set b[j] = 0;
                        }
                    }
                
                for (i in 0..N)
                {
                    let re3 = M(qs[i]);
                    if (re3 == One)
                    {
                        X(qs[i]);
                    }
                }
            }
            return b;
        }
    }
}
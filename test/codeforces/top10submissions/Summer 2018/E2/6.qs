namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (N : Int, Uf : ((Qubit[], Qubit) => ())) : Int[]
    {
        body
        {
            mutable b = new Int[N];
            mutable tmp = 1;
            using (qs = Qubit[N+1])
            {
                    for (j in 0..N)
                    {
                        let re = M(qs[j]);
                        if (re == One)
                        {
                            X(qs[j]);
                        }
                        if (tmp == 0)
                        {
                            set tmp = 1;
                        }
                        else
                        {
                            set tmp = 0;
                        }
                    }
                    Uf(qs[0..N-1], qs[N]);
                    
                    
                    for (i in 0..N-1)
                    {
                        set b[i] = 0;
                    }
                    
                    let re1 = M(qs[N]);
                    
                    
                    
                    if (re1 == Zero)
                    {
                        if (tmp == 1)
                        {
                            set b[0] = 1;
                        }
                    }
                    else
                    {
                        if (tmp == 0)
                        {
                            set b[0] = 1;
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
namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

   operation Solve1(qs : Qubit[]) : Unit {
    body (...) {
            for(i in 1..(Length(qs)-1))
            {
                CNOT(qs[0], qs[i]);
            }
            H(qs[0]);
            for(i in 1..(Length(qs)-1))
            {
                CNOT(qs[0], qs[i]);
            }
            }
            adjoint invert;
        controlled distribute;
        controlled adjoint distribute;
    }

    operation Solve (qs : Qubit[]) : Unit {
        for(i in 0..(ExpMod(2, Length(qs), 50)-2))
        {
            mutable j = ExpMod(2, Length(qs), 50)-2-i;
            
            if(j%2 == 0)
            {   
                mutable l = (j-(j%2))/2;
                for(k in 0..(Length(qs)-2))
                {
                    if(l%2 == 0)
                    {
                        X(qs[k+1]);
                    }
                    set l = (l-(l%2))/2;
                }
                Controlled X(qs[1..Length(qs)-1], qs[0]);
                Controlled H(qs[1..Length(qs)-1], qs[0]);
                set l = (j-(j%2))/2;
                for(k in 0..Length(qs)-2)
                {
                    if(l%2 == 0)
                    {
                        X(qs[k+1]);
                    }
                    set l = (l-(l%2))/2;
                }
            }
            else
            {
                using(qu=Qubit[1])
                {
                    mutable l = j;
                    for(k in 0..(Length(qs)-1))
                    {
                        if(l%2 == 0)
                        {
                            X(qs[k]);
                        }
                        set l = (l-(l%2))/2;
                    }
                    Controlled X(qs, qu[0]);
                    set l = j;
                    for(k in 0..(Length(qs)-1))
                    {
                        if(l%2 == 0)
                        {
                            X(qs[k]);
                        }
                        set l = (l-(l%2))/2;
                    }
                    set l = j+1;
                    for(k in 0..(Length(qs)-1))
                    {
                        if(l%2 == 0)
                        {
                            X(qs[k]);
                        }
                        set l = (l-(l%2))/2;   
                    }
                    Controlled X(qs, qu[0]);
                    set l = j+1;
                    for(k in 0..(Length(qs)-1))
                    {
                        if(l%2 == 0)
                        {
                            X(qs[k]);
                        }
                        set l = (l-(l%2))/2;
                    }
                    
                    set l = j;
                    mutable kl = 100;
                    for(k in 0..(Length(qs)-1))
                    {
                        if(l%2 == 0)
                        {
                            if(k < kl)
                            {
                                set kl = k;
                            }
                        }
                        set l = (l-(l%2))/2;
                    }

                    Controlled Solve1(qu[0..0], qs[0..kl]);

                    set l = j;
                    for(k in 0..(Length(qs)-1))
                    {
                        if(l%2 == 0)
                        {
                            X(qs[k]);
                        }
                        set l = (l-(l%2))/2;
                    }
                    Controlled X(qs, qu[0]);
                    set l = j;
                    for(k in 0..(Length(qs)-1))
                    {
                        if(l%2 == 0)
                        {
                            X(qs[k]);
                        }
                        set l = (l-(l%2))/2;
                    }
                    set l = j+1;
                    for(k in 0..(Length(qs)-1))
                    {
                        if(l%2 == 0)
                        {
                            X(qs[k]);
                        }
                        set l = (l-(l%2))/2;   
                    }
                    Controlled X(qs, qu[0]);
                    set l = j+1;
                    for(k in 0..(Length(qs)-1))
                    {
                        if(l%2 == 0)
                        {
                            X(qs[k]);
                        }
                        set l = (l-(l%2))/2;
                    }

                }
            }
        }
    } 	
}
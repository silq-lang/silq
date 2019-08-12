namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[], bits : Bool[][]) : Unit {
        using(qu = Qubit[2])
        {
            H(qu[0]);
            H(qu[1]);
            X(qu[0]);
            X(qu[1]);
            for(i in 0..(Length(qs)-1))
            {
                if(bits[0][i])
                {
                    CCNOT(qu[0], qu[1], qs[i]);
                }
            }
            X(qu[0]);
            X(qu[1]);

            X(qu[1]);
            for(i in 0..(Length(qs)-1))
            {
                if(bits[1][i])
                {
                    CCNOT(qu[0], qu[1], qs[i]);
                }
            }
            X(qu[1]);

            X(qu[0]);
            for(i in 0..(Length(qs)-1))
            {
                if(bits[2][i])
                {
                    CCNOT(qu[0], qu[1], qs[i]);
                }
            }
            X(qu[0]);

            for(i in 0..(Length(qs)-1))
            {
                if(bits[3][i])
                {
                    CCNOT(qu[0], qu[1], qs[i]);
                }
            }

            for(i in 0..(Length(qs)-1))
            {
                if(not bits[1][i])
                {
                    X(qs[i]);
                }
            }
            Controlled X(qs, qu[0]);
            for(i in 0..(Length(qs)-1))
            {
                if(not bits[1][i])
                {
                    X(qs[i]);
                }
            }

            for(i in 0..(Length(qs)-1))
            {
                if(not bits[2][i])
                {
                    X(qs[i]);
                }
            }
            Controlled X(qs, qu[1]);
            for(i in 0..(Length(qs)-1))
            {
                if(not bits[2][i])
                {
                    X(qs[i]);
                }
            }

            for(i in 0..(Length(qs)-1))
            {
                if(not bits[3][i])
                {
                    X(qs[i]);
                }
            }
            Controlled X(qs, qu[0]);
            Controlled X(qs, qu[1]);
            for(i in 0..(Length(qs)-1))
            {
                if(not bits[3][i])
                {
                    X(qs[i]);
                }
            }
        }
    }
}


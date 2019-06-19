namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
            using(qu = Qubit[8])
            {
                for(i in 1..((Length(x)-(Length(x)%2))/2))
                {
                        if(i == 1)
                        {
                            CCNOT(x[0], x[Length(x)-1], qu[7]);
                            X(x[0]);
                            X(x[Length(x)-1]);
                            CCNOT(x[0], x[Length(x)-1], qu[7]);
                            X(x[0]);
                            X(x[Length(x)-1]);
                        }
                        if(i == 2)
                        {
                            CCNOT(x[0], x[Length(x)-2], qu[3]);
                            CCNOT(x[1], x[Length(x)-1], qu[4]);
                            X(x[0]);
                            X(x[Length(x)-1]);
                            X(x[1]);
                            X(x[Length(x)-2]);
                            CCNOT(x[0], x[Length(x)-2], qu[3]);
                            CCNOT(x[1], x[Length(x)-1], qu[4]);
                            X(x[0]);
                            X(x[Length(x)-1]);
                            X(x[1]);
                            X(x[Length(x)-2]);
                            Controlled X(qu[3..4], qu[6]);
                        }
                        if(i == 3)
                        {
                            CCNOT(x[0], x[Length(x)-3], qu[2]);
                            CCNOT(x[1], x[Length(x)-2], qu[1]);
                            CCNOT(x[2], x[Length(x)-1], qu[0]);
                            X(x[0]);
                            X(x[Length(x)-1]);
                            X(x[1]);
                            X(x[Length(x)-2]);
                            X(x[2]);
                            X(x[Length(x)-3]);
                            CCNOT(x[0], x[Length(x)-3], qu[2]);
                            CCNOT(x[1], x[Length(x)-2], qu[1]);
                            CCNOT(x[2], x[Length(x)-1], qu[0]);
                            X(x[0]);
                            X(x[Length(x)-1]);
                            X(x[1]);
                            X(x[Length(x)-2]);
                            X(x[2]);
                            X(x[Length(x)-3]);
                            Controlled X(qu[0..2], qu[5]);
                        }
                }
                X(y);
                X(qu[5]);
                X(qu[6]);
                X(qu[7]);
                Controlled X(qu[8-((Length(x)-(Length(x)%2))/2)..7], y);
                X(qu[5]);
                X(qu[6]);
                X(qu[7]);
                for(i in 1..((Length(x)-(Length(x)%2))/2))
                {
                        if(i == 1)
                        {
                            CCNOT(x[0], x[Length(x)-1], qu[7]);
                            X(x[0]);
                            X(x[Length(x)-1]);
                            CCNOT(x[0], x[Length(x)-1], qu[7]);
                            X(x[0]);
                            X(x[Length(x)-1]);
                        }
                        if(i == 2)
                        {
                            Controlled X(qu[3..4], qu[6]);
                            CCNOT(x[0], x[Length(x)-2], qu[3]);
                            CCNOT(x[1], x[Length(x)-1], qu[4]);
                            X(x[0]);
                            X(x[Length(x)-1]);
                            X(x[1]);
                            X(x[Length(x)-2]);
                            CCNOT(x[0], x[Length(x)-2], qu[3]);
                            CCNOT(x[1], x[Length(x)-1], qu[4]);
                            X(x[0]);
                            X(x[Length(x)-1]);
                            X(x[1]);
                            X(x[Length(x)-2]);
                            
                        }
                        if(i == 3)
                        {
                            Controlled X(qu[0..2], qu[5]);
                            CCNOT(x[0], x[Length(x)-3], qu[2]);
                            CCNOT(x[1], x[Length(x)-2], qu[1]);
                            CCNOT(x[2], x[Length(x)-1], qu[0]);
                            X(x[0]);
                            X(x[Length(x)-1]);
                            X(x[1]);
                            X(x[Length(x)-2]);
                            X(x[2]);
                            X(x[Length(x)-3]);
                            CCNOT(x[0], x[Length(x)-3], qu[2]);
                            CCNOT(x[1], x[Length(x)-2], qu[1]);
                            CCNOT(x[2], x[Length(x)-1], qu[0]);
                            X(x[0]);
                            X(x[Length(x)-1]);
                            X(x[1]);
                            X(x[Length(x)-2]);
                            X(x[2]);
                            X(x[Length(x)-3]);
                            
                        }
                }
            }
        }
        adjoint auto;
    }
}
namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (q : Qubit) : Int {
        Rx(3.1415926535897/2.000, q);
        Ry(-1.0000*3.1415926535897/2.0000,q);
        mutable i = 0;
        using(qu = Qubit[1])
        {
            Controlled Ry([q], (2.000000*(0.95531661812), qu[0]));
            if(M(qu[0]) == One)
            {
                X(qu[0]);
                set i = 0;
            }
            else
            {
                H(q);
                if(M(q) == Zero)
                {
                    set i = 1;
                }
                else
                {
                    set i = 2;
                }
            }
        }
        return i;
    }
}
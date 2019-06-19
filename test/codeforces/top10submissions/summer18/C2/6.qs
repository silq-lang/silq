namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (q : Qubit) : Int
    {
        body
        {
            mutable ans = -1;
            using (qs = Qubit[1])
            {
                let re = M(qs[0]);
                if (re == One)
                {
                    X(qs[0]);
                }
                H(qs[0]);
                let re1 = M(qs[0]);
                if (re1 == Zero)
                {
                    let re2 = M(q);
                    if (re2 == One)
                    {
                        set ans = 1;
                    }
                }
                else
                {
                    H(q);
                    let re3 = M(q);
                    if (re3 == One)
                    {
                        set ans = 0;
                    }
                }
                
                let re4 = M(qs[0]);
                if (re4 == One)
                {
                    X(qs[0]);
                }
            }
            return ans;
        }
    }
}
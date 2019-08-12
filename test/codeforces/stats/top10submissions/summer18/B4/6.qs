namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
            H(qs[1]);
            CNOT(qs[0], qs[1]);
            H(qs[0]);
            let re1 = M(qs[0]);
            let re2 = M(qs[1]);
            mutable ans = 0;
            if (re1 == Zero)
            {
                if (re2 == Zero)
                {
                    set ans = 3;
                }
                else
                {
                    set ans = 1;
                }
            }
            else
            {
                if (re2 == Zero)
                {
                    set ans = 2;
                }
                else
                {
                    set ans = 0;
                }
            }
            return ans;
        }
    }
}
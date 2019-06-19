namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
            mutable ans = 0;
            H(qs[0]);
            H(qs[1]);
            let re1 = M(qs[0]);
            let re2 = M(qs[1]);
            if (re1 == Zero)
            {
                if (re2 == Zero)
                {
                    set ans = 0;
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
                    set ans = 3;
                }
            }
            return ans;
        }
    }
}
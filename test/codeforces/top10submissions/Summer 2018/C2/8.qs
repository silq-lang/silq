namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (q : Qubit) : Int
    {
        body
        {
            mutable ans=-1;
            using (r=Qubit[1]) {
                Reset(r[0]);
                H(r[0]);
                if (M(r[0])==Zero) {
                    if (M(q)==One) {
                        set ans=1;
                    }
                } else {
                    H(q);
                    if (M(q)==One) {
                        set ans=0;
                    }
                }
                Reset(r[0]);
            }
            return ans;
        }
    }
}
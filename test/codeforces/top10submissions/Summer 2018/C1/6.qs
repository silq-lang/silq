namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (q : Qubit) : Int
    {
        body
        {
            Ry(3.141592653589/4.0, q);
            let re = M(q);
            mutable ans = 0;
            if (re == One)
            {
                set ans = 1;
            }
            return ans;
        }
    }
}
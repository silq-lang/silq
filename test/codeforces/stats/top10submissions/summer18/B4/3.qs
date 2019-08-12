namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
            SWAP(qs[0], qs[1]);
            (Controlled Z)([qs[0]], qs[1]);
            H(qs[0]);
            H(qs[1]);
            let ans = ResultAsInt([M(qs[1]); M(qs[0])]);
            return 3 - ans;
        }
    }
}
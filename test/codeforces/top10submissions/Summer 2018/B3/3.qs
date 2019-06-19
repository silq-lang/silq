namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
            ApplyToEach(H, qs);
            let first = ResultAsInt([M(qs[0])]);
            let second = ResultAsInt([M(qs[1])]);
            return second + first * 2;
        }
    }
}
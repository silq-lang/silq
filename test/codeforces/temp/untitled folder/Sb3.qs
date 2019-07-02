namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
            // These states are produced by H x H, applied to four basis states.
            // To measure them, apply H x H followed by basis state measurement.
            H(qs[0]);
            H(qs[1]);
            return ResultAsInt([M(qs[1]), M(qs[0])]);
        }
    }
}
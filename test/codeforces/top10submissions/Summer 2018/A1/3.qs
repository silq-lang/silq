namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : ()
    {
        body
        {
            for (i in 0..Length(qs)-1) {
                H(qs[i]);
            }
        }
    }
}
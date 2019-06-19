namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : ()
    {
        body
        {
            ResetAll(qs);
            
            for(i in 1..Length(qs)){
                H(qs[i - 1]);
            }
        }
    }
}
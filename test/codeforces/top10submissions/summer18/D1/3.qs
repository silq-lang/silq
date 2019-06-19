namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[], y : Qubit, b : Int[]) : ()
    {
        body
        {
            let n = Length(x);
            for (i in 0..n-1) {
                if (b[i] == 1) {
                    CNOT(x[i], y);
                }
            }
        }
    }
}
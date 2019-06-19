namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Unit {
        for (k in 0..Length(qs)-1)
        {
            for (j in Length(qs)-1..-1..k+1)
            {
                X(qs[j]);
            }
            for (j in 0..k-1)
            {
                Controlled H(qs[k..Length(qs)-1], qs[j]);
            }
            for (j in Length(qs)-1..-1..k+1)
            {
                X(qs[j]);
            }
        }
    }
}


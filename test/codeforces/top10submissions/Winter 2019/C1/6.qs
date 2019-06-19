namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
            if (Length(x) == 1)
            {
                X(y);
            }
            else
            {
                using (qs = Qubit[Length(x)-1])
                {
                    for (i in 0..Length(x)-2)
                    {
                        CNOT(x[i], qs[i]);
                        CNOT(x[i+1], qs[i]);
                    }
                    Controlled X(qs[0..Length(x)-2], y);
                    for (i in 0..Length(x)-2)
                    {
                        CNOT(x[i], qs[i]);
                        CNOT(x[i+1], qs[i]);
                    }
                }
            }
        }
        adjoint auto;
    }
}
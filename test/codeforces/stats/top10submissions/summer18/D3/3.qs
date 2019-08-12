namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[], y : Qubit) : ()
    {
        body
        {
            X(y);
            CNOT(x[0], y);
            CNOT(x[1], y);
            CNOT(x[2], y);
            (Controlled X)(x, y);
            ApplyToEach(X, x);
            (Controlled X)(x, y);
            ApplyToEach(X, x);
        }
    }
}
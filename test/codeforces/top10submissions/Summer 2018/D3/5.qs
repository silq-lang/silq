namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[], y : Qubit) : ()
    {
        body
        {
            X(x[0]);
            (Controlled X)([x[0]; x[2]], x[1]);
            X(x[0]);
            
            X(x[0]);
            X(x[1]);
            (Controlled X)(x[0..1], x[2]);
            X(x[0]);
            X(x[1]);
            
            X(x[1]);
            X(x[2]);
            (Controlled X)(x[1..2], x[0]);
            X(x[1]);
            X(x[2]);
            
            CNOT(x[0], y);
            
            X(x[1]);
            X(x[2]);
            (Controlled X)(x[1..2], x[0]);
            X(x[1]);
            X(x[2]);
            
            X(x[0]);
            X(x[1]);
            (Controlled X)(x[0..1], x[2]);
            X(x[0]);
            X(x[1]);
            
            X(x[0]);
            (Controlled X)([x[0]; x[2]], x[1]);
            X(x[0]);
        }
    }
}
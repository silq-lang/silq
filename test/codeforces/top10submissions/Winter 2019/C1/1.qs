namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
            for (i in 1 .. 2 .. Length(x) - 1) {
                X(x[i]);
            }
            Controlled X(x, y);
            (ControlledOnInt(0, X))(x, y);
            for (i in 1 .. 2 .. Length(x) - 1) {
                X(x[i]);
            }
        }
        adjoint auto;
    }
}
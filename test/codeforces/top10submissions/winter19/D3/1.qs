namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Unit {
        Controlled MultiX([Head(qs)], Rest(qs));
        H(Head(qs));
        Controlled MultiX([Head(qs)], Rest(qs));
    }
}
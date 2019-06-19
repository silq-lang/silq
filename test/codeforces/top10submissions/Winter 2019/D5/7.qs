namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Unit {
        X(qs[0]);
        CCNOT(qs[0], qs[1], qs[2]);
        CCNOT(qs[0], qs[2], qs[1]);
        CCNOT(qs[0], qs[1], qs[2]);
        X(qs[0]);
        H(qs[0]);
        CNOT(qs[2], qs[1]);
        X(qs[1]);
        Controlled H(qs[1..1], qs[2]);
        X(qs[2]);
        CNOT(qs[2], qs[1]);
        X(qs[2]);
    }
}
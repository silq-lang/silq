namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Unit {
        CNOT(qs[1], qs[2]);
        CNOT(qs[2], qs[0]);
        CCNOT(qs[0], qs[2], qs[1]);
        X(qs[2]);
        (Controlled H)([qs[2]], qs[1]);
        X(qs[2]);
        H(qs[0]);
        CNOT(qs[1], qs[2]);
    }
}
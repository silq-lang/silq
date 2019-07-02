namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Unit {
        ApplyToEach(CNOT(qs[0], _), qs[1 .. Length(qs) - 1]);
        H(qs[0]);
        ApplyToEach(CNOT(qs[0], _), qs[1 .. Length(qs) - 1]);
    } 
}
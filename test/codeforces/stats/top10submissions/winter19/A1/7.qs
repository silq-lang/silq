namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Unit {
        Ry(2.000000*0.61547970867, qs[0]);
        X(qs[0]);
        Controlled H(qs[0..0], qs[1]);
        X(qs[0]);
    }
}

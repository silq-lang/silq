namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Extensions.Math;
    open Microsoft.Quantum.Extensions.Convert;

    operation Solve (qs : Qubit[]) : Unit {
        Ry(ArcCos(1.0/Sqrt(3.0))*2.0, qs[0]);
        Controlled H(qs[0..0], qs[1]);
        X(qs[0]);
    }
}



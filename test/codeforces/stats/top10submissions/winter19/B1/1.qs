namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Extensions.Math;
    open Microsoft.Quantum.Extensions.Diagnostics;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Int {
        let z = ComplexPolar(0.0, 0.0);
        let v1 = StatePreparationComplexCoefficients([z, ComplexPolar(6.27963030e-01, 0.0), ComplexPolar(6.27963030e-01, 0.0), z, ComplexPolar(-4.59700843e-01, 0.0)]);
        Adjoint v1(BigEndian(qs));
        MultiX(qs);
        Controlled Z(Rest(qs), qs[0]);
        MultiX(qs);
        v1(BigEndian(qs));
        let v2 = StatePreparationComplexCoefficients([z, ComplexPolar(-0.70710678, 0.0), ComplexPolar(0.70710678, 0.0)]);
        Adjoint v2(BigEndian(qs));
        MultiX(qs);
        Controlled S(Rest(qs), qs[0]);
        MultiX(qs);
        v2(BigEndian(qs));
        return ResultAsInt(MultiM(qs)) == 4 ? 0 | 1;
    }
}
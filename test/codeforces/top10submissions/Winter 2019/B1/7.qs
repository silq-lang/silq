namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Int {
        CNOT(qs[1], qs[2]);
        CNOT(qs[2], qs[1]);
        Controlled Rz(qs[2..2], (-2.0000*3.14159265359/3.000, qs[1]));
        Controlled H(qs[2..2], qs[1]);
        CNOT(qs[0], qs[2]);
        Ry(2.000000*0.61547970867, qs[0]);
        if(M(qs[2]) == One && M(qs[1]) == Zero && M(qs[0]) == Zero)
        {
            return 0;
        }
        return 1;
    }
}
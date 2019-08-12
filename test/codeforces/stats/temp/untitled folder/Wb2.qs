namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (q : Qubit) : Int {
        mutable output = 0;
        let alpha = ArcCos(Sqrt(2.0 / 3.0));

        using (a = Qubit()) {
            Z(q);
            CNOT(a, q);
            Controlled H([q], a);
            S(a);
            X(q);
            (ControlledOnInt(0, Ry))([a], (-2.0 * alpha, q));
            CNOT(a, q);
            Controlled H([q], a);
            CNOT(a, q);

            // finally, measure in the standard basis
            let res0 = MResetZ(a);
            let res1 = M(q);

            // dispatch on the cases
            if (res0 == Zero && res1 == Zero) {
                set output = 0;
            }
            elif (res0 == One && res1 == Zero) {
                set output = 1;
            }
            elif (res0 == Zero && res1 == One) {
                set output = 2;
            }
            else {
                // this should never occur
                set output = 3;
            }
        }
        
        return output;
    }
}
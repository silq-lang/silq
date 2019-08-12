namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Extensions.Math;
    open Microsoft.Quantum.Extensions.Convert;

    operation WState_Arbitrary_Reference (qs : Qubit[]) : Unit {
        body (...) {
            let N = Length(qs);

            if (N == 1) {
                X(qs[0]);
            } else {
                let theta = ArcSin(1.0 / Sqrt(ToDouble(N)));
                Ry(2.0 * theta, qs[0]);

                (ControlledOnInt(0, WState_Arbitrary_Reference))(qs[0 .. 0], qs[1 .. N - 1]);
            }
        }

        adjoint auto;
        controlled auto;
        controlled adjoint auto;
    }

    operation Solve (qs : Qubit[]) : Int {
        // map the first state to 000 state and the second one to something orthogonal to it
        R1(-2.0 * PI() / 3.0, qs[1]);
        R1(-4.0 * PI() / 3.0, qs[2]);
        Adjoint WState_Arbitrary_Reference(qs);
        return MeasureInteger(LittleEndian(qs)) == 0 ? 0 | 1;
    }
}
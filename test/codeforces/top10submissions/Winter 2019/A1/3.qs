namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Convert;
	open Microsoft.Quantum.Extensions.Math;

	operation WState (qs : Qubit[]) : Unit {
        body (...) {
            let n = Length(qs);
            if (n == 1) {
                X(qs[0]);
            } else {
                let theta = ArcSin(1.0 / Sqrt(ToDouble(n)));
                Ry(2.0 * theta, qs[0]);
                
                X(qs[0]);
                Controlled WState(qs[0 .. 0], qs[1 .. n - 1]);
                X(qs[0]);
            }
        }
        
        adjoint invert;
        controlled distribute;
        controlled adjoint distribute;
    }

    operation Solve (qs : Qubit[]) : Unit {
		body (...) {
			using (t = Qubit[1]) {
				WState([qs[0], qs[1], t[0]]);
				X(qs[0]); X(qs[1]);
				Controlled X (qs, t[0]);
				X(qs[0]); X(qs[1]);
			}
		}
		
    }
}
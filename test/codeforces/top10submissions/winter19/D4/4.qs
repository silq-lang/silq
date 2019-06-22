namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Diagnostics;
	open Microsoft.Quantum.Extensions.Convert;
	open Microsoft.Quantum.Extensions.Math;

	operation Help1 (qs : Qubit[]) : Unit {
		body (...) {
			if (Length(qs) > 0) {
				MultiX(qs);
				IntegerIncrementLE(-1, LittleEndian(qs));
			}
		}
		adjoint auto;
		controlled auto;
		adjoint controlled auto;
	}
	
	operation Help2 (qs : Qubit[]) : Unit {
		body (...) {
			if (Length(qs) > 0) {
				MultiX(qs);
				IntegerIncrementLE(1, LittleEndian(qs));
			}
		}
		adjoint auto;
		controlled auto;
		adjoint controlled auto;
	}

	operation Solve (qs : Qubit[]) : Unit {
        body (...) {
			if (Length(qs) > 0) {
				Controlled Help2([Tail(qs)], Most(qs));
				X(Tail(qs));
				Controlled Help1([Tail(qs)], Most(qs));
				X(Tail(qs));
				Controlled ApplyToEachCA([Tail(qs)], (X, Most(qs)));
				H(Tail(qs));
				Controlled ApplyToEachCA([Tail(qs)], (X, Most(qs)));
			}
        }
		adjoint auto;
		controlled auto;
		adjoint controlled auto;
    }

	// operation Test() : Unit {
	// 	using (qs = Qubit[10]) {
	// 		DumpMachine(());
	// 		ResetAll(qs);
	// 	}
	// }
}
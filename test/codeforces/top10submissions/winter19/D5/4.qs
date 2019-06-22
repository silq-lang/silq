namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Diagnostics;
	open Microsoft.Quantum.Extensions.Convert;
	open Microsoft.Quantum.Extensions.Math;
	
	operation Help1 (qs : Qubit[]) : Unit {
		body (...) {
			CNOT(qs[0], qs[1]);
			X(qs[1]);
			Controlled H([qs[1]], qs[0]);
			X(qs[1]);
			CNOT(qs[0], qs[1]);
			SWAP(qs[0], qs[1]);
		}
		adjoint auto;
		controlled auto;
		adjoint controlled auto;
	}
	
	operation Help2 (qs : Qubit[]) : Unit {
		body (...) {
			CNOT(qs[0], qs[1]);
			X(qs[1]);
			Controlled H([qs[1]], qs[0]);
			X(qs[1]);
			CNOT(qs[0], qs[1]);
		}
		adjoint auto;
		controlled auto;
		adjoint controlled auto;
	}

	operation Solve (qs : Qubit[]) : Unit {
        body (...) {
			if (Length(qs) > 0) {
				Controlled Help2([Head(qs)], Rest(qs));
				X(Head(qs));
				Controlled Help1([Head(qs)], Rest(qs));
				H(Head(qs));
			}
        }
		adjoint auto;
		controlled auto;
		adjoint controlled auto;
    }

	// operation Test() : Unit {
	// 	using (qs = Qubit[3]) {
	// 		DumpMachine(());
	// 		ResetAll(qs);
	// 	}
	// }
}
namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Diagnostics;
	open Microsoft.Quantum.Extensions.Convert;
	open Microsoft.Quantum.Extensions.Math;

	operation inc(qs : Qubit[]) : Unit {
		body (...) {
			if (Length(qs) > 1)
			{
				Controlled inc([Head(qs)], Rest(qs));
			}
			X(Head(qs));
		}

		adjoint auto;
		controlled auto;
		controlled adjoint auto;
	}

	operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
			let n = Length(x);

			using (qs = Qubit[4]) {
				
				for (q in x) {
					Controlled inc([q], qs);
				}
				
				(ControlledOnInt(0, X))(qs, y);
				(ControlledOnInt(3, X))(qs, y);
				(ControlledOnInt(6, X))(qs, y);
				(ControlledOnInt(9, X))(qs, y);

				for (q in x) {
					Controlled Adjoint inc([q], qs);
				}
			}
        }
		adjoint self;
		controlled auto;
		adjoint controlled auto;
    }

	// operation Test() : Unit {
	// 	using (qs = Qubit[10]) {
	// 		ApplyToEach(H, Most(qs));
	// 		Solve(Most(qs), Tail(qs));
	// 		DumpMachine(());
	// 		ResetAll(qs);
	// 	}
	// }
}
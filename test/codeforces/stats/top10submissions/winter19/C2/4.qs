namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Diagnostics;
	open Microsoft.Quantum.Extensions.Convert;
	open Microsoft.Quantum.Extensions.Math;

	operation Check(p : Int, x : Qubit[], y : Qubit) : Unit {
        body (...) {
			let n = Length(x);

			for (i in p..n-1) {
				CNOT(x[i % p], x[i]);
			}
			(ControlledOnInt(0, X))(x[p..n-1], y);
			for (i in p..n-1) {
				CNOT(x[i % p], x[i]);
			}
        }
		adjoint self;
		controlled auto;
		adjoint controlled auto;
	}

	operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
			let n = Length(x);

			using (a = Qubit[n - 1]) {
				for (p in 1..n-1) {
					Check(p, x, a[p - 1]);
				}
				X(y);
				(ControlledOnInt(0, X))(a, y);

				for (p in 1..n-1) {
					Check(p, x, a[p - 1]);
				}
			}
        }
		adjoint self;
		controlled auto;
		adjoint controlled auto;
    }

	// operation Test() : Unit {
	// 	using (qs = Qubit[8]) {
	// 		ApplyToEach(H, Most(qs));
	// 		Solve(Most(qs), Tail(qs));
	// 		DumpMachine(());
	// 		ResetAll(qs);
	// 	}
	// }
}
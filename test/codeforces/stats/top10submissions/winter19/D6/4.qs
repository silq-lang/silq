namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Diagnostics;
	open Microsoft.Quantum.Extensions.Convert;
	open Microsoft.Quantum.Extensions.Math;

	operation Solve (qs : Qubit[]) : Unit {
        body (...) {
			let n = Length(qs);
			for (k in (1<<<n)-2..-1..0) {
				let a = BoolArrFromPositiveInt(k, n);
				let b = BoolArrFromPositiveInt(k + 1, n);

				for (i in 1..n-1) {
					if (a[i] != b[i]) {
						CNOT(qs[0], qs[i]);
					}
					if (not b[i]) {
						X(qs[i]);
					}
				}

				Controlled H(qs[1..n-1], qs[0]);

				for (i in n-1..-1..1) {
					if (not b[i]) {
						X(qs[i]);
					}
					if (a[i] != b[i]) {
						CNOT(qs[0], qs[i]);
					}
				}
			}
        }
    }

	// operation Test() : Unit {
	// 	using (qs = Qubit[3]) {
	// 		DumpMachine(());
	// 		ResetAll(qs);
	// 	}
	// }
}
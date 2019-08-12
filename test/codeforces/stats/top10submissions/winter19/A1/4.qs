namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Diagnostics;
	open Microsoft.Quantum.Extensions.Convert;
	open Microsoft.Quantum.Extensions.Math;

    operation Solve (qs : Qubit[]) : Unit {
        body (...) {
			ApplyToEach(H, qs);
			using (q = Qubit()) {
				Controlled X(qs, q);
				Controlled ApplyToEachC([q], (H, qs));
				Reset(q);
			}
        }
    }

	// operation Test() : Unit {
	// 	using (qs = Qubit[2]) {
	// 		Solve(qs);
	// 		DumpMachine(());
	// 		ResetAll(qs);
	// 	}
	// }
}
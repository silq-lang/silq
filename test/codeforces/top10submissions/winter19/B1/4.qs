namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Diagnostics;
	open Microsoft.Quantum.Extensions.Convert;
	open Microsoft.Quantum.Extensions.Math;

	operation Prepare (qs : Qubit[]) : Unit {
		body (...) {
			Ry(2. * ArcCos(Sqrt(1. / 3.)), qs[0]);
			Controlled H([qs[0]], qs[1]);
			CCNOT(qs[0], qs[1], qs[2]);
			CNOT(qs[0], qs[1]);
			X(qs[0]);
		
			R1(2. * PI() / 3., qs[1]);
			R1(4. * PI() / 3., qs[2]);
		}

		adjoint auto;
	}

	operation Solve (qs : Qubit[]) : Int {
        body (...) {
			Adjoint Prepare(qs);
			return ResultAsInt(MultiM(qs)) == 0 ? 0 | 1;
        }
    }

	// operation Test() : Unit {
	// 	using (qs = Qubit[3]) {
	// 		DumpMachine(());
	// 		ResetAll(qs);
	// 	}
	// }
}
namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Diagnostics;
	open Microsoft.Quantum.Extensions.Convert;
	open Microsoft.Quantum.Extensions.Math;

	operation Thingy(q : Qubit) : Unit {
		body (...) {
			Rx(85220819. / 72025731., q);
			Ry(216827617. / 441709652., q);
			Rz(-94509533. / 132417409., q);
		}

		controlled auto;
		adjoint auto;
		controlled adjoint auto;
	}

	operation Solve (q : Qubit) : Int {
        body (...) {
			H(q);
			mutable res = -1;
			using (a = Qubit()) {
				CNOT(q, a);
				CNOT(a, q);
				Controlled Thingy([a], q);
				CNOT(a, q);
				CNOT(q, a);
				X(q);
				Controlled H([q], a);
				CNOT(a, q);

				set res = MeasureInteger(LittleEndian([q, a]));
			}

			return res;
		}
    }

	// operation Test() : Unit {
	// 	using (q = Qubit()) {
	// 		mutable cnt = 0;
	// 		for (i in 0..1000) {
	// 			H(q);
	// 			R1(4. * PI() / 3., q);
	// 			if (Solve(q) == 2) {
	// 				set cnt = cnt + 1;
	// 			}
	// 			Reset(q);
	// 		}
	// 		Message(ToStringI(cnt));
	// 	}
	// }
}
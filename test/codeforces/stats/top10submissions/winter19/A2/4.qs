namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Diagnostics;
	open Microsoft.Quantum.Extensions.Convert;
	open Microsoft.Quantum.Extensions.Math;

    operation Solve (qs : Qubit[], bits : Bool[][]) : Unit {
        body (...) {
			using (anc = Qubit[2]) {
				ApplyToEach(H, anc);
				Controlled ApplyPauliFromBitString(anc, (PauliX, true, bits[3], qs));
				X(anc[0]);
				Controlled ApplyPauliFromBitString(anc, (PauliX, true, bits[2], qs));
				X(anc[1]);
				Controlled ApplyPauliFromBitString(anc, (PauliX, true, bits[0], qs));
				X(anc[0]);
				Controlled ApplyPauliFromBitString(anc, (PauliX, true, bits[1], qs));
				X(anc[1]);
				(ControlledOnBitString(bits[1], X))(qs, anc[0]);
				(ControlledOnBitString(bits[2], X))(qs, anc[1]);
				(ControlledOnBitString(bits[3], X))(qs, anc[0]);
				(ControlledOnBitString(bits[3], X))(qs, anc[1]);
			}
        }
    }

	// operation Test() : Unit {
	// 	using (qs = Qubit[3]) {
	// 		Solve(qs, [[false, false, false], [false, false, true], [false, true, false], [true, false, false]]);
	// 		DumpMachine(());
	// 		ResetAll(qs);
	// 	}
	// }
}
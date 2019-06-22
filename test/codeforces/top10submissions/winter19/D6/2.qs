namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Convert;

	operation Incre (qs : Qubit[]) : Unit {
		body (...) {
			let n = Length(qs);
			for (i in n-1..-1..0) {
				(Controlled X) (qs[0..i-1], qs[i]);
			}
		}
		adjoint auto;
	}

	// operation Add_slow (qs : Qubit[], V : Int) : Unit {
	// 	body (...) {
	// 		for (i in 0..V-1) {
	// 			Incre(qs);
	// 		}
	// 	}
	// 	adjoint auto;
	// }

	operation Add (qs : Qubit[], V : Int) : Unit {
		body (...) {
			let b = BigIntToBools(ToBigInt(V));
			let n = Length(b);
			let m = Length(qs);
			for (i in 0..n-1) {
				if (b[i] == true) {
					Incre(qs[i..m-1]);
				}
			}
		}
		adjoint auto;
	}

    operation Solve (qs : Qubit[]) : Unit {
		let n = Length(qs);
		let N = 2^n;
		for (i in N-2..-1..0) {
			(Adjoint Add) (qs, i);
			for (j in 1..n-1) {
				X(qs[j]);
			}
			(Controlled H) (qs[1..n-1], qs[0]);
			for (j in 1..n-1) {
				X(qs[j]);
			}
			Add(qs, i);
		}
    }
}
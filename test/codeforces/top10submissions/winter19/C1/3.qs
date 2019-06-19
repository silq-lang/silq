namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

	operation SetDiffs (x : Qubit[], t : Qubit[]) : Unit {
		body (...) {
			let n = Length(t);
			for (i in 0..n-1) {
				CNOT(x[i], t[i]);
				CNOT(x[i+1], t[i]);
			}
		}
		adjoint auto;
	}
    

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
            let n = Length(x);
			if (n==1) {
				X(y);
			} else {
				using (t = Qubit[n-1]) {
					SetDiffs(x, t);
					Controlled X (t, y);
					Adjoint SetDiffs(x, t);
				}
			}
        }
        adjoint auto;
    }
}
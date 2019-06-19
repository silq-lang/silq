namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

	operation BitwiseRightShift (qs : Qubit[]) : Unit {
		body (...) {
			let n = Length(qs);
			if (n==1) {
				X(qs[0]);
			} else {
				BitwiseRightShift(qs[0..n-2]);
				Controlled X(qs[0..n-2], qs[n-1]);
			}
		}	
		adjoint auto;
		controlled auto;
	}

	operation BitwiseLeftShift (qs : Qubit[]) : Unit {
		body (...) {
			Adjoint BitwiseRightShift(qs);
		}	
		adjoint auto;
		controlled auto;
	}

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
            let n = Length(x);
			using (r = Qubit[4]) {
				for (i in 0..3) {X(r[i]);}
				for (i in 0..n-1) {Controlled BitwiseRightShift([x[i]], r);}
				Controlled X(r, y);
				for (i in 1..9) {
					BitwiseLeftShift(r);
					if (i%3==0){
						Controlled X(r, y);
					}
				}
				for (i in 1..9) {BitwiseRightShift(r);}
				for (i in 0..n-1) {Controlled BitwiseLeftShift([x[i]], r);}
				for (i in 0..3) {X(r[i]);}
			}
        }
        adjoint auto;
    }
}
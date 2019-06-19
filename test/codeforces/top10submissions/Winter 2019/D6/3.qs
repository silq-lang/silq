namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Convert;
	open Microsoft.Quantum.Extensions.Math;
	open Microsoft.Quantum.Extensions.Diagnostics;

	operation BitwiseRightShift (qs : Qubit[]) : Unit {
		body (...) {
			let n = Length(qs);
			if (n==1) {
				X(qs[0]);
			} else {
				//Controlled X(qs[1..n-1], qs[0]);
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

    operation Solve (qs : Qubit[]) : Unit {
		body (...) {
			let n = Length(qs);
			for (i in 0..(2^n)-3) {
				Controlled H(qs[1..n-1], qs[0]);
				BitwiseLeftShift(qs);
			}
			Controlled H(qs[1..n-1], qs[0]);
			for (i in 0..(2^n)-3) {
				BitwiseRightShift(qs);
			}	
		}
    }
}
namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Diagnostics;
	open Microsoft.Quantum.Extensions.Convert;
	open Microsoft.Quantum.Extensions.Math;

	function get1(n : Int) : Bool[] {
		mutable arr = new Bool[n];
		for (i in 0..2..n-1) {
			set arr[i] = not arr[i];
		}
		return arr;
	}

	function get2(n : Int) : Bool[] {
		mutable arr = new Bool[n];
		for (i in 1..2..n-1) {
			set arr[i] = not arr[i];
		}
		return arr;
	}

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
			(ControlledOnBitString(get1(Length(x)), X))(x, y);
			(ControlledOnBitString(get2(Length(x)), X))(x, y);
        }
		adjoint auto;
		controlled auto;
		adjoint controlled auto;
    }

	// operation Test() : Unit {
	// 	using (qs = Qubit[4]) {
	// 		H(qs[0]);
	// 		H(qs[1]);
	// 		H(qs[2]);
	// 		Solve(Most(qs), Tail(qs));
	// 		DumpMachine(());
	// 		ResetAll(qs);
	// 	}
	// }
}
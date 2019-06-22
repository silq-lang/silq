namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Diagnostics;
	open Microsoft.Quantum.Extensions.Convert;
	open Microsoft.Quantum.Extensions.Math;

	// function get1(n : Int) : Bool[] {
	// 	mutable arr = new Bool[n];
	// 	for (i in 0..2..n-1) {
	// 		set arr[i] = not arr[i];
	// 	}
	// 	return arr;
	// }

	// function get2(n : Int) : Bool[] {
	// 	mutable arr = new Bool[n];
	// 	for (i in 1..2..n-1) {
	// 		set arr[i] = not arr[i];
	// 	}
	// 	return arr;
	// }

	operation Solve (qs : Qubit[]) : Unit {
        body (...) {
			if (Length(qs) > 0) {
				Controlled ApplyToEachCA([Tail(qs)], (X, Most(qs)));
				H(Tail(qs));
				Controlled ApplyToEachCA([Tail(qs)], (X, Most(qs)));
			}
        }
		adjoint auto;
		controlled auto;
		adjoint controlled auto;
    }

	// operation Test() : Unit {
	// 	using (qs = Qubit[4]) {
	// 		Solve(qs);
	// 		DumpMachine(());
	// 		ResetAll(qs);
	// 	}
	// }
}
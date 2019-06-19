namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Convert;
	open Microsoft.Quantum.Extensions.Math;


	operation FlipOneBit(qs: Qubit[], x1: BigInt, x2: BigInt) : Unit {
		body (...) {
			let b1 = BigIntToBools_Correct(x1);
			let b2 = BigIntToBools_Correct(x2);
			let n = Length(qs);
			mutable idx = -1;
			for (i in 0..n-1) {if(b1[i] != b2[i]) {set idx=i;}}
			for (i in 0..n-1) {if (i!=idx && not b1[i]) {X(qs[i]);} }
			Controlled X(qs[0..idx-1]+qs[idx+1..n-1], qs[idx]);
			for (i in 0..n-1) {if (i!=idx && not b2[i]) {X(qs[i]);} }
		}
	}

	operation BigIntToBools_Correct(x: BigInt): Bool[] {
		mutable result = new Bool[20];
		mutable v = x;
		for(i in 0..15) {
			if (v % 2L == 1L) {set result[i] = true;}
			set v = v / 2L;
		}
		return result;
	}

	operation BoolsToBigInt_Correct(x: Bool[]): BigInt {
		mutable result = 0L;
		mutable pow = 1L;
		for (i in 0..Length(x)-1) {
			if (x[i]) {set result = result + pow;}
			set pow = pow * 2L;
		}
		return result;
	}

	operation Exchange(qs: Qubit[], x1: BigInt, x2: BigInt) : Unit {
		body (...) {
			let n = Length(qs);
			
			mutable path = new BigInt[20];
			set path[0] = x1;
			mutable pathLength = 1;
			mutable b1 = BigIntToBools_Correct(x1);
			mutable b2 = BigIntToBools_Correct(x2);
			for (i in 0..n-1) {
				if (b1[i] != b2[i]) {
					set b1[i] = b2[i];
					set path[pathLength] = BoolsToBigInt_Correct(b1);
					set pathLength = pathLength + 1;
				}
			}
			for (i in 0..pathLength-2) {
				FlipOneBit(qs, path[i], path[i+1]);
			}
			for (i in pathLength-2..-1..1) {
				FlipOneBit(qs, path[i], path[i-1]);
			}
		}
	}

	operation Sort(x: BigInt[]) : BigInt[] {
		mutable ans = x;
		let n = Length(ans);
		for (i in n-1..-1..1) {
			for (j in 1..i) {
				if (ans[j-1]>ans[j]) {
					let t = ans[j-1];
					set ans[j-1] = ans[j];
					set ans[j] = t;
				}
			}
		}
		return ans;
	}

    operation Solve (qs : Qubit[], bits : Bool[][]) : Unit {
		body (...) {
			mutable x = new BigInt[4];
			for (i in 0..3) {set x[i] = BoolsToBigInt_Correct(bits[i]); }

			let n = Length(qs);
			H(qs[0]);
			H(qs[1]);
			set x = Sort(x);
			for (i in 3..-1..0) {Exchange(qs, ToBigInt(i), x[i]);  }		
		}
    }
}
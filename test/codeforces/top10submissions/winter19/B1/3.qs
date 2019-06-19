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

	operation WState (qs : Qubit[]) : Unit {
        body (...) {
            let n = Length(qs);
            if (n == 1) {
                X(qs[0]);
            } else {
                let theta = ArcSin(1.0 / Sqrt(ToDouble(n)));
                Ry(2.0 * theta, qs[0]);
                
                X(qs[0]);
                Controlled WState(qs[0 .. 0], qs[1 .. n - 1]);
                X(qs[0]);
            }
        }
        
        adjoint invert;
        controlled distribute;
        controlled adjoint distribute;
    }

	operation MakePsi (qs : Qubit[], sign: Double) : Unit {
		body (...) { 
			WState(qs);
			let theta = 2.0*PI()/3.0;
			R1(theta*sign, qs[2]);
			R1(-theta*sign, qs[1]);
		}
		adjoint auto;
    }

    operation Solve (qs : Qubit[]) : Int {
		body (...) { 
			//MakePsi(qs, -1.0);
			Adjoint MakePsi(qs, 1.0);
			Exchange(qs, ToBigInt(2), ToBigInt(5));
			if (M(qs[0]) == Zero) {return 1;} else {return 0;}
		}
    }
}
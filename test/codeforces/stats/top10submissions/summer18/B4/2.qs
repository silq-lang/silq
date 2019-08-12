namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
            H(qs[1]);
			CNOT(qs[0], qs[1]);
			mutable res = 0;
			let res1 = M(qs[1]);
			if (res1 == One)
			{
				set res = res + 2;			
			}
			H(qs[0]);
			let res0 = M(qs[0]);
			if (res0 == One)
			{
				set res = res + 1;
			}
			return 3-res;
        }
    }
}
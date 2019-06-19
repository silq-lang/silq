namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
            H(qs[0]);
			H(qs[1]);
			let r0 = M(qs[0]);
			let r1 = M(qs[1]);
			mutable res = 0;
			if (r0 == One)
			{
				set res = res + 2;
			}
			if (r1 == One)
			{
				set res = res + 1;
			}
			return res;
        }
    }
}
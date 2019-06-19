namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
			mutable flag = 0;
            for (i in 0..Length(qs)-1)
			{
				let res = M(qs[i]);
				if (res == One)
				{
					set flag = 1;
				}
			}
			return flag;
        }
    }
}
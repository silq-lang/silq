namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (q : Qubit) : Int
    {
        body
        {
            Ry(3.141592653589/4., q);
			let res = M(q);
			if (res == One)
			{
				return 1;
			}
			else {
				return 0;
			}
        }
    }
}
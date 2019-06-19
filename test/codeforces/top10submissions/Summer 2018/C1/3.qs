namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (q : Qubit) : Int
    {
        body
        {
            let pi = 3.1415926536;
            Ry(pi / 8.0, q);
            return ResultAsInt([M(q)]);
        }
    }
}
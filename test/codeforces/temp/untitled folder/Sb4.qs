namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    // Helper function to implement diag(-1, 1, 1, 1)
    operation ApplyDiag (qs : Qubit[]) : ()
    {
        body
        {
            ApplyToEach(X, qs);
            (Controlled Z)([qs[0]], qs[1]);
            ApplyToEach(X, qs);
        }
            adjoint self;
        }
    
    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
            SWAP(qs[0], qs[1]); // pi
            With(ApplyDiag, ApplyToEach(H, _), qs); // diag(..) (H \otimes H) diag(..)
            return ResultAsInt([M(qs[1]), M(qs[0])]);
            
        } 
    }
}
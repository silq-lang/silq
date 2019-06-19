def arcsin(q:!ℝ) lifted :!ℝ;
def sqrt(q:!ℝ) lifted :!ℝ;

def solve(q0:𝔹,q1:𝔹) {
    q0 := H(q0);
    q1 := H(q1);
    q := 0:𝔹;
    
    if (q0 && q1){
        q := X(q);
    }
    
    if q {
        (q0, q1) := (H(q0), H(q1));
    }

    measure(q);
    return (q0, q1);
}
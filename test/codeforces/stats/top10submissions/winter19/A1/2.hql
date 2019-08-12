def arccos(q:!ℝ) lifted :!ℝ;
def sqrt(q:!ℝ) lifted :!ℝ;

def solve(q0:𝔹, q1:𝔹) {
    q0 := rotY(2.0 * arccos(sqrt(2.0/3.0)), q0);
    if !q0{
        q1 := H(q1);
    }
    return (X(q0), q1);
}

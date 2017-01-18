![alt text](https://raw.githubusercontent.com/eth-srl/psi/master/logo.png "PSI solver")

# PSI Solver

PSI is a tool for performing exact inference on probabilistic programs.
Given a probabilistic program, the tool produces an expression for the joint posterior distribution of the expressions computed by the program.

PSI is described in the paper 'PSI: Exact Symbolic Inference for Probabilistic Programs' (available at http://psisolver.org).

## Compatibility Disclaimer

PSI does not currently try to make any guarantees on backwards compatibility.
If your project depends on PSI, write down the exact commit hash to ensure others can reproduce your results.
The commit of HEAD at build time is displayed when running ./psi --help.

## Build Instructions

### GNU/Linux

#### Quick build

1. Run 'dependencies.sh' to download the DMD D compiler from http://downloads.dlang.org/releases/2.x/2.072.2/dmd.2.072.2.linux.zip and unzip it.

2. Run 'build.sh' to build PSI.

##### Additional information

PSI is written in the D programming language. D compilers are available at http://dlang.org/download.html.

./build.sh will use DMD inside the PSI directory if it exists, otherwise it will attempt to use DMD from your path.

./build.sh creates a debug build.
./build-release creates a release build.

*NOTE:* The tests do not currently pass with the release build (PSI computes equivalent, but different expressions).
(There is a nondeterministic-order-of-iteration issue.)

### Other platforms

The build instructions given here are for GNU/Linux. PSI also works on other platforms.
Feel free to write a pull request with working build scripts for your favourite platform.

### Example

```
$ ./dependencies.sh && ./build.sh
```

## Running the tests

```
cd test
./runtests
```


*NOTE:* The tests will currently only pass with the debug build. (See Build Instructions.)

## Using PSI on your own models

Run './psi example.prb', where 'example.prb' is a file containing the source code for the model.
The next section ("Quick language guide") briefly introduces the most important language features.

### Additional command-line options

Run './psi --help' to display information about supported command-line options.


### Examples

```
$ cat example.prb
def main(){
    a := Gauss(0,1);
    b := Gauss(0,1);
    return if a > b { a } else { b };
}

$ psi example.prb
p(r₁) = (d/dx)⁻¹[e^(-x²)](r₁·⅟√2̅)·2·⅟e^(r₁²·⅟2)·⅟π·⅟√2̅

$ psi example.prb --mathematica --cdf
p[r₁_] := (-2^(1/2)*Sqrt[Pi]*(Erf[-1/2^(1/2)*20]+1)/2^2+1/2^(1/2)*2*Sqrt[Pi]*(Erf[1/2^(1/2)*cr1]+1)/2^2)*1/2^(1/2)*1/Pi*Boole[-20+-cr1<=0]

$ cat coin_bias_small.prb
def main(){
    p := Uniform(0,1);
    x1 := Bernoulli(p);
    observe(x1==1);
    x2 := Bernoulli(p);
    observe(x2==0);
    x3 := Bernoulli(p);
    observe(x3==1);
    return p;
}

$ psi coin_bias_small.prb --plot
p(p) = (-30·p+30)·[-1+p≤0]·[-p≤0]·p⁴
plotting... (PDF)
command: 
set pointsize 20
set xlabel "p"
set ylabel "density"
set samples 500, 500
set isosample 200
unset key
plot [-10:10] (-1+x<=0)*(-30*x+30)*(-x<=0)*x**4
```

## Quick language guide

PSI operates on files with the *.prb extension.

Such a file contains one or multiple procedure definitions:

```
def procedureName(param1,param2,...,paramn){
    statements
}
```

There should be a procedure of name 'main', denoting the program entry and exit point.

### Statements

Function bodies consist of a sequence of statements, possibly referencing the variables param1,param2,...,paramn.

- variable := expression; introduces a new variable of name 'variable'

- variable = expression; assigns to an existing variable. +=, -=, *=, /=, div= and %= are also supported.

- if expression { statements } else { statements } is a conditional. 'else { statements }' is optional

- repeat expression { statements } repeats the given statements a number of times given by the expression. The expression should be an integer constant.

- for variable in [start..end){ statement } is a for-loop over a range. Start and end should be integer constants.
  If the exact number of iterations is not known ahead of time, an if statment can be nested within the for loop in order
  to cut off some of the iterations.

- observe(expression); conditions the joint probability distribution of the program variables on the event that the expression is not equal to zero
  *Note:* The probability that the expression is not equal to zero should be positive (enforced by PSI during normalization).
  
- cobserve(expression,value); conditions the joint probability distribution of the program variables on the event that the given expression
  equals the given value. The probability that the variable is equal to the expression must be zero, but the probability density at that point
  must be positive. *Note:* This is not currently enforced automatically by PSI, therefore some care is required when using this primitive.

- assert(expression); puts the program in the error state in case the expression is not equal to zero (PSI will then report the probability of error).

- return (expression1,expression2,...,expressionn); terminates the procedure with the given results.
  If no return statement is provided at the end of a procedure, return (); is automatically inserted.

### Special statements

- a := readCSV(filename); where filename is a string literal (such as "data.csv"), reads the given file containing a comma-separated list of values
  into a read-only array 'a'. Indexing into such arrays requires deterministic integer indices.


### Expressions

- The following operators are supported and denote the corresponding operations on real numbers with standard C operator precedence (where applicable):
  expression + expression, expression - expression, expression * expression, expression / expression, expression div expression, expression | expression, expression ⊕ expression, expression & expression

  -expression

  expression < expression, expression > expression, expression <= expression, expression >= expression,
  expression == expression, expression != expression

(div is integer division. "a div b" is the same as "floor(a/b)". ⊕ is bitwise xor. The non-unicode syntax is "a xorb b".)

- There are logical operators !, && and ||, also with standard C operator precedence.
  (Warning: && and || do not currently use short-circuit evaluation.)

- Conditional expressions are supported: if expression { expression } else { expression }. Only one branch is evaluated.

- Expressions can be parenthesized in order to change order of precedence, e.g. a*(b+c).

### Primitive Distributions

Primitive distributions can be sampled arbitrarily within expressions. They are exposed as procedures with special names.
If arguments don't conform to the constraints of the distribution, the program enters the error state.

- Gauss(mean,variance) samples from the Gaussian distribution with the given mean and non-negative variance.

- Uniform(a,b) samples an uniform real number between a and b, with a<=b.

- Bernoulli(p) is 1 with probability p and 0 with probability 1-p, where 0<=p<=1.

- UniformInt(a,b) samples an uniform integer between a and b. There should be at least one integer n with a<=n<=b.

- Categorical(p) is i with probability p[i] for i in [0..p.length). p should be an array of real numbers of positive length.

- Exponential(rate) samples from the Exponential distribution with the given positive rate (inverse scale).

- Beta(alpha,beta) samples from the Beta distribution with the given positive shape parameters.

- Gamma(shape,rate) samples from the Gamma distribution with the given shape and rate.

- Laplace(mean,scale) samples from the Laplace distribution with the given mean and positive scale.

- Pareto(shape,scale) samples from the Pareto distribution with the given shape and scale which should be positive real numbers.

- StudentT(degrees\_of\_freedom) samples from the StudentT distribution with the given positive degrees of freedom parameter.

- Weibull(scale,shape) samples from the Weibull distribution with the given positive scale and shape parameters.

- Rayleigh(sigma_squared) samples from the Rayleigh distribution with the given non-negative squared scale parameter.

- Poisson(mean) samples from the Poisson distribution with the given positive mean.
  (At this time, expect less-than optimal simplification from PSI for expressions generated by programs sampling from this distribution.)

### Built-in deterministic functions
- floor, ceil, exp, log, abs.

### Special Expressions

- FromMarginal(expression1,expression2,...,expressionn)
  Samples an n-tuple of values with the same marginal joint probability distribution as the existing expressions expression1,...,expressionn,
  the sampled tuple is however independent of all existing variables.

- SampleFrom("(variable1,...,variablen;parameter1,...,parameterm) => pdf",argument1,...,argumentm)
  This primitive samples an n-tuple of values from the given probability density function.
  The density function can depend both on the values and a set of parameters. To specify the pdf, the
  mathematical operators +-*/^, the constant e, the dirac delta 'delta(expr)', absolute values |expression|
  and Iverson brackets of the shape [expression<=expression], [expression<expression], [expression=expression]
  and [expression != expression] can be used, among others.

  Example:
  ```
  x := SampleFrom("(x;y) => [-y<=x]*[x<=y]*x^2",y);
  (x,y,z) := SampleFrom("(x,y,z;w) => [-1<=x]*[x<=1]*[-1<=y]*[y<=1]*|x|*|y|*delta(z-w)",w);
  ```  
  *Note:* PSI does not currently verify that the given density expression is in fact a generalized probability density, so
  some care is required when using this primitive.
  
- Expectation(expression)
  Returns the expectation of the given expression conditioned on the current path in the program.
  *Note:* PSI does not currently verify that the expectation of the given expression in fact exists,
  so some care is required when using this primitive. (e.g. Expectation(Gauss(0,1)/Gauss(0,1)) does not converge.)



### Experimental language features

#### Exponentiation

Exponentiation is supported as expression ^ expression and expression ^= expression.
*Note:* PSI does not currently check whether (a,b) is in the domain of exponentiation on real numbers.

#### Method calls and tuples

```
def swapped(a,b){
    return (b,a);
}

def main(){
    (z,w) = swapped(1,2);
    return ((z,w),swapped(z,w)); // p(r₁,r₂) = δ_r₁[(2,1)]·δ_r₂[(1,2)]
}
```

#### Type annotations

Any expression can be annotated with a type using the (expression : Type) annotation.

A type can be R (real numbers), a Type[], the type of a tuple Type1 x Type2 x ... x Typen, or the name of a custom data type (see below).
The empty tuple has type '1'.

One can annotate method return types:

```
def main(): R x R{
    return (0,1);
}
```

#### General arrays

```
x := [1,2,3]; // declare array
return x[UniformInt(0,2)]; // index randomly into array

x := ([] : R[]); // declare empty array of real numbers
y := x ~ [1]; // y is the concatenation of x with [1]. ~= is also supported

z := array(UniformInt(1,3),[1,2,3]); // declare array of arrays of random size, initialized with [1,2,3] at all indices
```

*Note:* PSI does not currently verify that array indices and lengths are integers.
(Indexing into an array using a non-integer index within [0..length) returns the value 0.)

The length of an array 'a' can be obtained using the expression 'a.length'.

*Note:* General arrays are not compatible with arrays obtained using the 'x := array(n)' special construct.
In order to bypass the special casing, use e.g. 'x := array(n,0)'.

#### Data abstraction

E.g.

```
dat Foo{
    x : R;
    y : R[];
    def Foo(x: R, y: R[]){ // constructor
        this.x = x;
        this.y = y;
    }
    def method(){
        y[1]+=y[0];
        y[0]+=x;
        return (x,y[0]);
    }
}

def main(){
    x := Foo(1,[1,2,3]);
    return x.method(); // p(r₁) = δ_r₁[(1,2)]
}
```

## Source Code Guide

This section gives a quick overview of the source code.

psi.d:
  
  Contains the program entry point, interprets the command line arguments and calls the other components.

expression.d, type.d, declaration.d:
  
  Contains the declaration of source language AST nodes.

lexer.d, parser.d:
  
  Lexer and parser for the source language.
  (*Note:* Contains some cruft as it was quickly adapted from a parser for the D programming language.)

semantic_.d:
  
  Semantic analyzer, performs type checking and annotates the AST generated by the parser.

backend.d:
  
  Defines the backend interface.

symbolic.d:
  
  Symbolic backend. Translates the annotated AST to distribution expressions.

distrib.d:
  
  Contains the declaration of generalized probability density functions for the primitive distributions supported by PSI.
  Furthermore, this file contains the class Distribution which encapsulates a probability distribution over program variables with an additional error state.

dexpr.d:
  
  Contains the implementation of the intermediate language of distribution expressions and most of the simplification code.

dparse.d:
  
  Parser for distribution expressions.
  (Used for debugging and the sampleFrom primitive, aims to invert the default toString method for distribution expressions, while also allowing different notations).

differentiation.d:
  
  Symbolic differentiation engine.

integration.d:
  
  Symbolic integration engine.

summation.d:
  
  Symbolically evaluates sum expressions.

limits.d, asymptotics.d:
  
  Limit evaluation engine.

terminal.d:
  
  Simple colored terminal output.

hashtable.d:
  
  Hash table implementation with optimization for small tables.

help.d:
  
  Implements the --help option and a few other options.

util.d:
  
  Utility functions not available in the standard library (not everything in this file is used by PSI).

## Adding new tests

Add a *.prb file into the 'test' directory. 

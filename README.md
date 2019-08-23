# typeless.git

`typeless.git` is a simple lambda calculus evaluator that comes with four basic concepts:

1. Variables. Anything that is not a paranthesis, the word "lambda", a semicolon, an equals sign,
   and the word "print" is considered a variable.
2. Lambdas. These are S-expressions of the form `(lambda <var> <s-expr>)`
3. Applictaions. These are S-expressions of the form `(<s-expr> <s-expr>...)`
4. Definitions. These are expressions of the form `<var> = <s-expr>;`.

Typeless was created to experiment with converting recursive code into iterative code.
You can read more about the process in my blog here: [Recursion Elimination - Or how to make pretty code ugly](https://blog.grgz.me/posts/recursion_elimination.html)

Make sure to check `stdlib.lc` for some predefined functions on integers, booleans, and lists.
The standard library makes use of Church encodings since the basic concepts do not include integers,
booleans, nor lists.

It's possible to launch a repl or interpret a given file. If you wish to interpret a file then the
executed code is the one defined for `main`. So you must have a definition
`main = (print (fib 12));` for example in your code.

Error reporting is really bad, so don't rely on it.

You can build the interpreter with `dub build`.

You can launch the interpreter with `dub run`, and you can interpret a file with
`dub run - stdlib.lc`.
Or you can use the built binary: `./typeless` and `./typeless stdlib.c` respectively.

### Usage

The synopsis is

```
typeless [--debug] [-e] [-b] [-d] [-r] [-p] [FILE]

OPTIONS
    -e          use the optimized (iterative) version of the evaluator
    -b          use the optimized (iterative) beta reduction
    -d          use the optimized (iterative) term duplication function
    -r          always start the REPL regardless of the contents of FILE
    -p          use the partial evaluator instead of the evaluator (recursive)
                renders -e -b -d useless, will always use optimized beta and recursive dup
    --debug     print every step of the evaluation
    FILE        Optional. The file to interpret.
                If the file contains a main function then this function is called.
                If the file doesn't contain a main function then the REPL is opened.
                If no file was provided the REPL is also opened.

EXAMPLE
    ./typeless -b stdlib.lc
    ./typeless -p <(cat stdlib.lc; echo "; main = rec-pow 5;")
```

### License

This work is licensed under the GPLv3 license. Make sure to read the `COPYING` file at the root of
the project

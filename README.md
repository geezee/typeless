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

### License

This work is licensed under the GPLv3 license. Make sure to read the `COPYING` file at the root of
the project

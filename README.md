# bidirectional-impl

Proof-of concept implementation of the type inference and elaboration algorithm for type classes with Bidirectional Type Class Instances. Once you have built the executable `prototype` using your favorite tool, you can call it on files with

    prototype <filename>

You can find examples of input files in folder `Tests`, illustrating the syntax the prototype accepts. The above command either fails (if the program is ill-typed), or prints the following:

1. The elaborated program
2. The inferred Haskell type of the "main" program (top-level expression at the end of the file)
3. The program theory (all rules generated by class and instance declarations)
4. The inferred System FC type of the "main" program (top-level expression at the end of the file)

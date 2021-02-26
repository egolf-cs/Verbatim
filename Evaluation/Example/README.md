# Performance Evaluation

## Compilation
First compile Verbatim according to "../README.md". This will automatically extract the relevant code from Coq to OCaml and place it in the proper directory.

Then compile the evaluation executable:
~~~
ocamlopt -O3 -w -20 -w -26 -o instancedriver instance.mli instance.ml instancedriver.ml
~~~
We compiled using the 4.11.0+flambda version of OCaml.

## I/O
~~~
mkdir data results
~~~
Place your input json data into the data folder. The results will be placed in the results folder.

## Execution
To execute the evaluation driver, run
~~~
./instancedriver
~~~

## Visualization
Once the driver has finished executing, the results can be visualized with
~~~
python3 plot.py
~~~
This requires the python3 libraries matplotlib and numpy.

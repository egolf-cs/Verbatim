
# < Args handling
while test $# -gt 0
do
    case "$1" in
        -l) lex_type=Literal
            driver=lit_driver.ml
            ;;
        -s) lex_type=Semantic
            driver=sem_driver.ml
            ;;
        -*) echo "Bad option: -s for semantic or -l for literal"
            ;;
        *) lang=$1
            ;;
    esac
    shift
done

if [ -z $lang ]
then
    echo "Bad args: You did not specify a language. E.g: './compile_extracted.sh -l JSON'"
    exit
fi

if [ -z $lex_type ]
then
    echo "Bad args: You did not specify an option: -s for semantic or -l for literal"
    exit
fi
# />

# < Path/file handling
bad_path_msg="Bad path: Extract your lexer as '../../$lang/Evaluation/$lex_type/instance.ml'"

if [ ! -d ../../$lang ]
then
    echo $bad_path_msg
    exit
fi

if [ ! -d ../../$lang/Evaluation ]
then
    echo $bad_path_msg
    exit
fi

if [ ! -d ../../$lang/Evaluation/$lex_type ]
then
    echo $bad_path_msg
    exit
fi

if [ ! -d ../../$lang/Evaluation/$lex_type/data ]
then
    mkdir ../../$lang/Evaluation/$lex_type/data
fi

if [ ! -d ../../$lang/Evaluation/$lex_type/results ]
then
    mkdir ../../$lang/Evaluation/$lex_type/results
fi

if [ ! -f ../../$lang/Evaluation/$lex_type/instance.ml ]
then
    echo $bad_path_msg
    exit
fi
# />

# < Compile the OCaml
path=../../$lang/Evaluation/$lex_type
ocamlopt -O3 -w -20 -w -26 -g -I $path $path/instance.mli $path/instance.ml common.ml $driver -o $path/evaluate
# />

# < Create symbolic link to plot.py
ln plot.py $path/plot.py
# />

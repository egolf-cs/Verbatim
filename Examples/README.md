# Using Verbatim

## Introduction

Suppose we want to create a lexer for a language LANG. This file explains how to instantiate such a lexer in Coq, extract that Coq code to OCaml, compile the extracted OCaml code, run the resulting executable on a set of benchmark files, and plot the results. 

This README file is located in the directory Examples. That directory is where all lexers should live. We will copy the Template directory and its contents to a new directory Examples/LANG. We will refer to this directory simply as LANG.

## Instantiation

The directory LANG/Lexer contains two files Literal.v and Semantic.v. The file Literal.v is where we define the Label type and the list of lexical rules. The file Semantic.v is where we define semantic actions. The vast majority of these files can/should remain unchanged. Comments within the files should make it clear what should be changed by the user. The file Examples/\_Utils.Lexer.v includes useful helper functions for building lexical rules.

## Extraction

At the bottoms of LANG/Literal.v and LANG/Semantic.v there are two extraction commands. The paths in these commands must be changed to reflect the change in language. The best way to compute the path is to run "Compute (extract_path "LANG" Literal)" or "Compute (extract_path "LANG" Semantic)", depending on which file we are modifying.

The resulting path is relative to the location of Verbatim's Makefile. What this means is that running the extraction command interactively will fail; we must add the LANG/\*.v files to the \_CoqProject file. 

The Extraction command will fail during build unless we do "mkdir Examples/LANG/Evaluation/Literal" and "mkdir Examples/LANG/Evaluation/Semantic" because these are the directories where the extracted code will live.

## Compilation

We now navigate to Examples/\_Utils/Evaluation. This is where the ml code for the drivers lives. It is also where compile_extracted.sh and clean.sh live. 

To link the extracted ocaml with the driver code, we must run "./compile_extracted.sh LANG -l" for the Literal lexer or "./compile_extracted.sh LANG -s" for the semantic lexer. This will create an executable file "Examples/LANG/Evaluation/{Literal/ | Semantic}/evaluate". In the same directory it will also create a symbolic link to plot.py and the directories data and results.

## Evaluation

We will need to populate "Examples/LANG/Evaluation/Literal/data" and "Examples/LANG/Evaluation/Semantic/data" with our benchmarking data. When we run ./evaluate, it will put the results in the results folder. To plot the results, we simply run python3 plot.py.

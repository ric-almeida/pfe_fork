# PHD

Playground for my PhD, mostly bigraphs in Coq

To compile:

First create CoqMakefile:

    coq_makefile -f _CoqProject -o CoqMakefile

Then compile with

    make -f CoqMakefile

To generate LaTeX documentation: 

    coqdoc -g -toc --latex --lib-subtitles src/ConcreteBigraphs.v

To clean:

Run

    ./coqclean.sh

If necessary: 

    chmod +x coqclean.sh


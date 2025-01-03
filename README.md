** THIS IS A FORK OF https://gitlab.isae-supaero.fr/c.marcon/pfe AND NOT MY WORK **
This branch currently only adds an example bigraph instantiated in BiCoq. It's based
on the virus-and-firewall network model from https://bitbucket.org/uog-bigraph/bigraph-tools/src/master/bigrapher/examples/virus-multifirewall.big
-----------------------------------------------------------------------------------

# PHD

Playground for my PhD, mostly bigraphs in Coq

To compile:

First create CoqMakefile:

    coq_makefile -f _CoqProject -o CoqMakefile

Then compile with

    make -f CoqMakefile

To generate LaTeX documentation: 

    coqdoc -g -toc --latex --lib-subtitles src/AbstractBigraphs.v

To clean:

Run

    ./coqclean.sh

If necessary: 

    chmod +x coqclean.sh


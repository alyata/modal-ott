# Formalisation of a modal dependent type theory using OTT

## Requirements:
- ocaml with `opam`
- `coq` installed from source to enable 
  [external package extension support](https://github.com/coq/platform#installation)
- `ott` with the [`coq-ott` extension](https://github.com/ott-lang/ott#to-install-and-build)
- LaTeX (only if you want to compile birk_star.tex locally)

## Coq Output
```
# Generate the coq definitions from ott
> ott -i birk_star.ott -o birk_star.v

# Compile the coq files
> coq_makefile -f _CoqProject -o Makefile
> make

# Clean the generated coq compile files
> make cleanall
```

## LaTeX Output
```
# Generate the LaTeX file from ott
> ott -i birk_star.ott -o birk_star.tex

# Compile using xeLaTeX to have fontawesome support
> xelatex birk_star.tex

# Clean the generated LaTeX compile files
> latexmk -C
```
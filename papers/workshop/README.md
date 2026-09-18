# Dissertation LaTeX Template

> Authors: Pierre Le Bras with input from Stefano Padilla and Manuel Maarek
> Heriot-Watt University, Computer Science Department
> Last update: September 2025

> Original ACM template: Association for Computing Machinery (ACM), used under [LaTeX Project Public License v1.3 (LPPL-1.3)](https://www.latex-project.org/lppl.txt)
> The ACM template was used as the styling basis and modified in `main.tex` and `format.tex` to make it correspond with the Computer Science Department's dissertation format.

## Structure

The template project is structured as follows:
 - `main.tex` is the main file, pulling content from other files to create the full document for your submission. This is the default rendered file. **This is the main file that you should edit**.
 - `template` is a folder containing several files used to create the template (pulling packages, laying out the title page, etc.). These files are then pulled into `main.tex`. **You should not modify `main.tex` where a template file is imported** (with the `\input` command). **You also must not modify the content of files in the `template` directory**.
 - `acm_format` is a folder containing files produced by the ACM to format their conference and journal submissions. **You must not modify the content of files in the `acm_format` directory**.
 - The `images` and `code` directories should be used to store, respectively, images or code snippets used in `main.tex`.
 - `references.bib` is where you must add the BibTex entries for your list of references.
 - `examples.tex` contains LaTeX examples that you can reuse in the dissertation.

## Getting Started

 1. Create a copy of this project in Overleaf: Menu -> Copy Project. (Alternatively, you can download the sources and use them offline)
 2. Edit the macros at the top of `main.tex` to change the author name, title of dissertation, name of supervisor, etc.
 3. Write the dissertation in `main.tex`. Refer to the examples file to learn how to include specific elements (figures, code listings, tables, cross-references, etc.).
    - The sample chapters should be a good starting point to structure the dissertation
    - Add appendices at the end of `main.tex`
    - Add references to `references.bib`
 4. Complete the abstract and acknowledgements sections
 5. Read through the document to check everything is in order

The `examples.tex` file includes examples of the following LaTeX features:
 - Text
 - Section structure
 - Lists, numbered and unnumbered
 - Tables
 - Figures, including having subfigures
 - Equations
 - Pseudo-code
 - Code listing (directly from code files)
 - Labelling and cross-referencing
 - Citations

To change the referencing style, go to `template/references.tex` and comment/uncomment lines to switch between ACM, Harvard, or APA styles. You can switch between ACM Author-Year or ACM Numeric in `template/acm_settings.tex`.
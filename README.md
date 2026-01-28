# Project Euler Statements

This repo contains [Project Euler](https://projecteuler.net) problem statements, downloaded and convert to Markdown

This repo was created to have a better input data source to feed LLMs to try and solve and Lean autoformalize all Project Euler problems in one go.

The main reasons for creating this repo are:

* stop pinging their server without need
* Codex CLI sometimes tells me it can't access the problem statement. I'm not sure if this is due to robots.txt like restrictions or other restrictions. I don't know and I don't want to know.
* I don't like feeding their ugly HTML to my poor LLMs :-) They deserve some nice markdown!

Together with the solutions from https://github.com/lucky-bai/projecteuler-solutions this makes for a nice little mathematics dataset :-)

Generate the data:

```python
virtualenv -p python3 .venv 
. .venv/bin/activate
pip install -r requirements.txt
./download.sh
./html2md.py
./extract_metadata.py
```

Folders:

* [data/minimal](data/minimal): HTML from `https://projecteuler.net/minimal=X` e.g. https://projecteuler.net/minimal=949
* [data/problem](data/problem): HTML from `https://projecteuler.net/problem=X` e.g. https://projecteuler.net/problem=949
* [data/documents](data/documents): files from under `https://projecteuler.net/resources/documents/` e.g. https://projecteuler.net/resources/documents/0042_words.txt at [data/documents/0042_words.txt](data/documents/0042_words.txt). These are required as input data to solve some of the problems.
* [data/md](data/md): local conversion of the above HTML downloads to a nice Markdown format
* [data/lean](data/lean): formal [Lean](https://lean-lang.org/) statements of the problems
* [data/meta](data/meta): JSON problem metadata extracted from the HTML e.g.: [data/meta/1.json](data/meta/1.json) contains:

  ```
  {
    "title": "Multiples of 3 or 5",
    "date": "2001-10-05T18:00:00"
  }
  ```

## Lean

Best Lean autoformalization prompt so far:

```
Convert Project Euler 3 ../md/3.md statement into a formal lean statement in ProjectEulerStatements/P3.lean. Put all definitions of that lean file under namespace ProjectEulerStatements.P3. Produce the simplest naive function which matches the problem statement as close as possible and name it "naive". noncomputable funcitons are fine, but partial is not, if you have partial also produce a proof of termination. If you find two close approaches name the second one "naive2". Add lean "example" statements with native_decide as asserts for any test values given in the problem statement. Ensure that lake -R build works for that file.
```

We have manually inspected the following statements to ensure that they match up with Project Euler statements: **all up to 3**. TODOs:

* 4: is kind of horrible

## Licenses

* [data/](data/): CC BY-NC-SA 4.0 as per Project Euler's license https://projecteuler.net/copyright
* code: BSD 3-Clause

Tested on Python 3.13.7, Ubuntu 25.10.

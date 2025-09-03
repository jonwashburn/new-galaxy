# Gravity-Derived FULL Package

This bundle contains papers, scripts, environment files, data (Rotmod_LTG), minimal results, and the formal Lean file to reproduce the paper figures and example.

## Layout
- paper/: LaTeX sources and PDFs
- scripts/: Python and shell scripts
- env/: Python requirements
- data/Rotmod_LTG/: SPARC-like rotation curves (dat files)
- results/: Minimal artifacts (e.g., sparc_master.pkl, example_rc.pdf)
- formal/: IndisputableMonolith.lean (formal scaffolding)
- docs/: auxiliary notes

## Quickstart
1) Create a Python 3.10+ environment and install requirements:
   Requirement already satisfied: pip in ./.venv/lib/python3.9/site-packages (21.2.4)
Collecting pip
  Using cached pip-25.2-py3-none-any.whl (1.8 MB)
Installing collected packages: pip
  Attempting uninstall: pip
    Found existing installation: pip 21.2.4
    Uninstalling pip-21.2.4:
      Successfully uninstalled pip-21.2.4
Successfully installed pip-25.2
2) Build master table and example figure:
   
3) Compile the LaTeX paper(s) (requires a TeX distribution):
   


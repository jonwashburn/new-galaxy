# Gravity-Derived Release Bundle

Contents:
- paper/: LaTeX sources and any compiled PDFs present
- scripts/: Core scripts to rebuild master table and example figure
- results/: Minimal artifacts if available (sparc_master.pkl, example_rc.pdf)

Quickstart:
1. Create a Python environment (>=3.10) with numpy, pandas, matplotlib.
2. From scripts/, run:
   - `python build_sparc_master_table.py`
   - `python plot_example_rc.py` (emits ../results/example_rc.pdf)

Notes:
- SPARC rotmod data should be available at active/data/Rotmod_LTG (see repo README).
- For full figures/tables and baseline comparisons, see the repository and companion paper.

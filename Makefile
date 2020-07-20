# Test
# fstar.exe Test1.fst --load FEM.Process --tactics_info

.PHONY: all
all: FEM.Process.fst.cmxs

.PHONY: FEM.Process.fst
FEM.Process.fst:

FEM.Process.fst.checked: FEM.Process.fst
	fstar.exe --admit_smt_queries true --cache_checked_modules FEM.Process.fst

FEM_Process.ml: FEM.Process.fst.checked
	fstar.exe --codegen Plugin --extract_module FEM.Process FEM.Process.fst

.PHONY: FEM.Process.fst.cmxs
FEM.Process.fst.cmxs: FEM_Process.ml

.PHONY: clean
clean:
	rm -f *.ml *.cmxs *.cmi *.cmx *.o *.checked

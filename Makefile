fstar.exe --codegen Plugin --extract FEM.Process.fst FEM.Process.fst
fstar.exe --codegen Plugin --extract_module FEM.Process FEM.Process.fst
--load FEM.Process

fstar.exe --load FEM.Process FEM.Test.fst

fstar.exe --load FEM.Process FEM.Test.fst

# Compilation
fstar.exe --cache_checked_modules FEM.Process.fst
fstar.exe --codegen Plugin --extract_module FEM.Process FEM.Process.fst

fstar.exe --admit_smt_queries true --load FEM.Process Test1.fst

fstar.exe --admit_smt_queries true --use_native_tactics $HOME/fstar-extended-mode Test1.fst

fstar.exe --admit_smt_queries true --load FEM.Process --use_native_tactics $HOME/fstar-extended-mode Test1.fst


fstar.exe --cache_checked_modules FEM.PTests.fst
fstar.exe --codegen Plugin --extract_module FEM.PTests FEM.PTests.fst

fstar.exe --load FEM.PTests Test1.fst

# Build
fstar.exe --cache_checked_modules FEM.Process.fst && fstar.exe --codegen Plugin --extract_module FEM.Process FEM.Process.fst

# Test
fstar.exe Test1.fst --load FEM.Process --tactics_info

# Clean
rm -f *.ml *.cmxs *.cmi *.cmx *.o

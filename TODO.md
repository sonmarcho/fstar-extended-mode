* implement general functions to detect the equivalent of ST.get () to find proper state variable instantations
* the generation of the global pre/postconditions is often random because I don't have any control on the effects
* the export to the *Messages* buffer is not safe:
  * it would be good to be able to export to another dedicated buffer
  * the format is not safe: we should add a suffix to all the occurrences of '\n' when we export a term or a message
* sometimes the effects are unfolded too much, leading to unexploitable pre/postconditions
* it is better to use a "magic witness" rather than "admit" for the global pre/post (because of effects problems)
* when cleaning:
  * `logical` (Type0)
  * `Pervasives.Native.Some`
  * `op_Negation`
  * current module?
* effect analysis doesn't always work: use the effect from the binding instead? Or try to remove lifts. Or at least add special treatment for assertions.
  -> don't use tcc on the whole term, but strip its arguments and use tcc on its head in order to retrieve the "purest" effect
* change the way the target effect is instantiated: do it incrementally, not all at once
* debug return type in functor init in Hacl.Streaming.SHA2
* would be nice to be able to normalize projectors, tuples inlinings

# Main limitations
* the output is the *Messages* buffer (fragile AND not convenient)
* FEM.Process is not automatically loaded in interactive mode
* the effects are somtimes out of control
  * tcc often returns lifted effects (but I think I have a - tedious - workaround)
  * I need to be able to retrieve the signature (as written by the user) of the function I'm about to post-process
* (pretty) printing is a problem:
  * the printed terms are sometimes not valid (i.e.: we can't parse them) because they may contain identifiers not accessible to the user (ex.: Prims.logical, FStar.UInt32.__uint_to_t...)
  * fully named identifiers (FStar.List.Tot....) clutter the printed assertions: it would be good to be able not to use full names when possible (ex.: don't use it if the module is in scope and there is no ambiguity, use abbreviation if the user defined one)
  * ascriptions often clutter the terms (but I can fix that at the meta level, by filtering the ascriptions)
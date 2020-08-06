* implement general functions to detect the equivalent of ST.get () to find proper state variable instantations
* the generation of the global pre/postconditions is often random because I don't have any control on the effects
* the export to the *Messages* buffer is not safe:
  * it would be good to be able to export to another dedicated buffer
  * the format is not safe: we should add a suffix to all the occurrences of '\n' when we export a term or a message
* sometimes the effects are unfolded too much, leading to unexploitable pre/postconditions
* it is better to use a "magic witness" rather than "admit" for the global pre/post (because of effects problems)
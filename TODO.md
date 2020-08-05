* implement general functions to detect the equivalent of ST.get () to find proper state variable instantations
* the generation of the global postcondition sometimes doesn't work
* the export to the *Messages* buffer is not safe:
  * it would be good to be able to export to another dedicated buffer
  * the format is not safe: we should add a suffix to all the occurrences of '\n' when we export a term or a message
* sometimes the effects are unfolded too much, leading to unexploitable pre/postconditions

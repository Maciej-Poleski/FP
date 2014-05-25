type label = string
datatype lterm = Number of (IntInf.int)
                        |Label of label
                        |App of lterm*lterm
                        |Abs of label*lterm
                        |Let of ((label*lterm) list) * lterm;

fun lterm2str term = "Jakis term";


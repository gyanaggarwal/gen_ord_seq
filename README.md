# gen_ord_seq
A simple general-purpose functional data structure

This data structure is very similar to Finger Trees (Ralf Hinze and Ross Paterson)
in terms of its behavior but differs in actual implementation.

This data structure also supports adding/removing of elements to the ends in amortized constant time and general enough to support deque, ordered sequence (unique/non-unique), ordered map (unique/non-unique), priority queue etc.

This has been implemented in Erlang as a behavior that has 3 callback functions.
The actual implementation of these callback functions are provided by specific implementations.

We have included here the following erlang modules:
 
 gen_ord_seq.erl        -  behavior module
 os_deque.erl           -  deque implementation module
 os_ordered_seq.erl     -  ordered_seq (unique/non-unique) and 
                           ordered_map (unique/non-unique) implementation module
 os_priority_queue.erl  -  priority queue implementation module
 os_demo.erl            -  demo module

Please refer to document provided in doc folder for more information.
-module(os_deque).
-author("gyanendra aggarwal").

-behavior(gen_ord_seq).

-export([new/1, len/1, is_empty/1, nth/2, 
         in_l/2, in_r/2, out_l/1, out_r/1, 
         from_list_l/2, from_list_r/2, to_list_l/1, to_list_l/2, to_list_r/1, to_list_r/2,
         join/2, fast_join/2, split/2]).

-export([measure/1, null/0, add/2]).

-define(TYPE, ?MODULE).

-type os_deque() :: term().

-spec new(NodeSize :: integer()) -> os_deque().
new(NodeSize) ->
  gen_ord_seq:new(?TYPE, NodeSize, undefined).

-spec len(T :: os_deque()) -> integer().
len(T) ->
  gen_ord_seq:len(T).

-spec is_empty(T :: os_deque()) -> true | false.
is_empty(T) ->
  gen_ord_seq:is_empty(T).

-spec in_l(A :: term(), T :: os_deque()) -> os_deque().
in_l(A, T) ->
  gen_ord_seq:cons_l(?MODULE, A, T).

-spec in_r(A :: term(), T :: os_deque()) -> os_deque().
in_r(A, T) ->
  gen_ord_seq:cons_r(?MODULE, A, T).

-spec out_l(T :: os_deque()) -> {{value, term()} | empty, os_deque()}.
out_l(T) ->
  gen_ord_seq:uncons_l(?MODULE, T).

-spec out_r(T :: os_deque()) -> {{value, term()} | empty, os_deque()}.
out_r(T) ->
  gen_ord_seq:uncons_r(?MODULE, T).
  
-spec from_list_l(Size :: integer(), L :: list()) -> os_deque().
from_list_l(Size, L) ->
  gen_ord_seq:from_list_l(?MODULE, L, new(Size)).

-spec from_list_r(Size :: integer(), L :: list()) -> os_deque().
from_list_r(Size, L) ->
  gen_ord_seq:from_list_r(?MODULE, L, new(Size)).

-spec to_list_l(T :: os_deque(), L :: list()) -> list().
to_list_l(T, L) ->
  gen_ord_seq:to_list_l(T, L).

-spec to_list_l(T :: os_deque()) -> list().
to_list_l(T) ->
  to_list_l(T, []).

-spec to_list_r(T :: os_deque(), L :: list()) -> list().
to_list_r(T, L) ->
  gen_ord_seq:to_list_r(T, L).

-spec to_list_r(T :: os_deque()) -> list().
to_list_r(T) ->
  to_list_r(T, []).

-spec join(T1 :: os_deque(), T2 :: os_deque()) -> os_deque().
join(T1, T2) ->
  gen_ord_seq:join(?MODULE, T1, T2).

-spec fast_join(T1 :: os_deque(), T2 :: os_deque()) -> os_deque().
fast_join(T1, T2) ->
  gen_ord_seq:fast_join(?MODULE, T1, T2).

-spec split(N :: integer(), T :: os_deque()) -> {os_deque(), os_deque()}.
split(N, T) ->
  gen_ord_seq:split(?MODULE, gen_ord_seq:pred_fun(fun erlang:'=<'/2, N), T).

-spec nth(N :: integer(), T :: os_deque()) -> {value, term()} | undefined.
nth(N, T) ->
  {L, _R} = split(N, T),
  case len(L) =:= N of
    true  -> case out_r(L) of 
                {empty, _} -> undefined;
                {{value, Value}, _} -> {value, Value}
             end; 
    false -> undefined
  end.

-spec measure(Arg :: term()) -> 1.
measure(_) -> 
  1.

-spec null() -> 0.
null()     -> 
  0.

-spec add(A :: integer(), B :: integer()) -> integer(). 
add(A, B)  -> 
  A+B.


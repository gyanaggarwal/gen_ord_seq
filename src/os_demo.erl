-module(os_demo).

-author("gyanendra aggarwal").

-export([perf_out_all/2, perf_out/2, 
         perf_in_l/3, perf_in_r/3]). 

% {[1000, 10000, 50000, 100000], 50}
perf_out_all(L, NodeSize) ->
  lists:foldl(fun(A, N) -> perf_out(A, N), N end, NodeSize, L),
  ok.

% {1000, 50}, {10000, 50}, {50000, 50}, {100000, 50}
perf_out(N, NodeSize) ->
  L0 = lists:seq(1, N),
  Q0 = os_deque:from_list_r(NodeSize, L0),

  {TLH, {{value, H}, _}} = timer:tc(fun list_out_l/1, [L0]),
  {TQH, {{value, H}, _}} = timer:tc(os_deque, out_l, [Q0]),
  {TLL, {{value, L}, _}} = timer:tc(fun list_out_r/1, [L0]),
  {TQL, {{value, L}, _}} = timer:tc(os_deque, out_r, [Q0]),

  io:format("elements=~p, \tqueue head=~p, \tlist head=~p, \tqueue last=~p, \tlist last=~p~n",
            [L, TQH, TLH, TQL, TLL]).

list_out_r(L0) ->
  [V | L1] = lists:reverse(L0),
  {{value, V}, lists:reverse(L1)}.

list_out_l(L0) ->
  [V | L1] = L0,
  {{value, V}, L1}.

% {50000, 50, 15}
perf_in_r(N, NodeSize, NR) ->
  L0 = lists:seq(1, N),
  LR = lists:seq(1, NR),
  Q0 = os_deque:from_list_r(NodeSize, L0),
  lists:foldl(fun(A, Acc) -> cons_r(A, Acc) end, {L0, Q0}, LR),
  ok.

cons_r(N, {L0, Q0}) ->
  {TL1, L1} = timer:tc(fun(A, Acc) -> Acc ++ [A] end, [N, L0]),
  {TQ1, Q1} = timer:tc(os_deque, in_r, [N, Q0]),
  io:format("entry=~p, \tlist=~p, \tqueue=~p~n", [N, TL1, TQ1]),
  {L1, Q1}.

% {50000, 50, 15}
perf_in_l(N, NodeSize, NR) ->
  L0 = lists:seq(1, N),
  LR = lists:seq(1, NR),
  Q0 = os_deque:from_list_r(NodeSize, L0),
  lists:foldl(fun(A, Acc) -> cons_l(A, Acc) end, {L0, Q0}, LR),
  ok.

cons_l(N, {L0, Q0}) ->
  {TL1, L1} = timer:tc(fun(A, Acc) -> [A | Acc] end, [N, L0]),
  {TQ1, Q1} = timer:tc(os_deque, in_l, [N, Q0]),
  io:format("entry=~p, \tlist=~p, \tqueue=~p~n", [N, TL1, TQ1]),
  {L1, Q1}.


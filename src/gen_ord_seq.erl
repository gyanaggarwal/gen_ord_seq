%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Licensed to the Apache Software Foundation (ASF) under one
% or more contributor license agreements.  See the NOTICE file
% distributed with this work for additional information
% regarding copyright ownership.  The ASF licenses this file
% to you under the Apache License, Version 2.0 (the
% "License"); you may not use this file except in compliance
% with the License.  You may obtain a copy of the License at
%
%   http://www.apache.org/licenses/LICENSE-2.0
%
% Unless required by applicable law or agreed to in writing,
% software distributed under the License is distributed on an
% "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
% KIND, either express or implied.  See the License for the
% specific language governing permissions and limitations
% under the License.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-module(gen_ord_seq).
-author("gyanendra aggarwal").

-export([new/3, get_attribute/1, is_empty/1, len/1, is_similar/2, 
         pred_fun/2,
         cons_l/3, cons_r/3, uncons_l/2, uncons_r/2, 
         from_list_l/3, from_list_r/3, to_list_l/2, to_list_r/2,
         join_l/3, join_r/3, join/3, fast_join/3, split/3]).

-callback measure(Arg :: term()) -> term().
-callback null() -> term().
-callback add(Arg1 :: term(), Arg2 :: term()) -> term().

-type measure()     :: {integer(), term()}.
-type module_name() :: atom().
-type node_type()   :: left_node | right_node.

-record(node, {type :: node_type(), 
                       measured :: measure(), 
                       list :: list()}).

-record(tree, {type :: atom(), 
               node_size :: integer(), 
               attribute :: term(), 
               measured :: measure(), 
               left_node :: #node{}, 
               trunk :: #tree{}, 
               right_node :: #node{}}).

-spec new(Type :: atom(), NodeSize :: integer(), Attribute :: term()) -> #tree{}.
new(Type, NodeSize, Attribute) ->
  #tree{type=Type, node_size=NodeSize, attribute=Attribute}.

-spec len_node(Node :: #node{} | undefined) -> integer().
len_node(undefined) ->
  0;
len_node(#node{measured=undefined}) ->
  0;
len_node(#node{measured={Length, _}}) ->
  Length.

-spec get_attribute(Tree :: #tree{} | undefined) -> term() | undefined.
get_attribute(undefined) ->
  undefined;
get_attribute(#tree{attribute=Attribute}) ->
  Attribute.

-spec len(Tree :: #tree{} | undefined) -> integer().
len(undefined) ->
  0;
len(#tree{measured=undefined}) ->
  0;
len(#tree{measured={Length,_}}) ->
  Length.

-spec is_empty(Tree :: #tree{} | undefined) -> true | false.
is_empty(undefined) ->
  true;
is_empty(T = #tree{}) ->
  len(T) =:= 0.

-spec is_similar(T1 :: #tree{}, T2 :: #tree{}) -> true | false.
is_similar(#tree{type=Type, attribute=Attribute}, 
           #tree{type=Type, attribute=Attribute}) ->
  true;
is_similar(_T1, _T2) ->
  false.

-spec split_list_at(NodeSize :: integer(), Len :: integer()) -> integer().
split_list_at(NodeSize, Len) ->
  Len-NodeSize.

-spec merge_required(NodeSize :: integer(), Len1 :: integer(), Len2 :: integer()) -> true | false.
merge_required(NodeSize, Len1, Len2) ->
  Len1 < NodeSize orelse Len2 < NodeSize.

-spec pred_fun(Cmp :: fun(), K :: term()) -> fun().
pred_fun(Cmp, K) ->
  fun(A) -> Cmp(A, K) end.

-spec measure_len(Mod :: module_name(), A :: term()) -> {1, term()}.
measure_len(Mod, A) -> {1, Mod:measure(A)}.

-spec null_len(Mod :: module_name()) -> {0, term()}.
null_len(Mod) -> {0, Mod:null()}.

-spec add_len(Mod :: module_name(), Arg1 :: measure(), Arg2 :: measure()) -> measure().
add_len(Mod, {A1, A2}, {B1, B2}) -> {A1+B1, Mod:add(A2, B2)}.

-spec split_pred_len(SplitPred :: fun(), Arg :: {term(), term()}) -> true | false.
split_pred_len(SplitPred, {_A1, A2}) -> SplitPred(A2).

-spec measure(Mod :: module_name(), Arg :: #node{} | #tree{} | undefined) -> measure().
measure(Mod, undefined) ->
  null_len(Mod);
measure(Mod, #node{measured=undefined}) ->
  null_len(Mod);
measure(_Mod, #node{measured=V}) ->
  V;
measure(Mod, #tree{measured=undefined}) ->
  null_len(Mod);
measure(_Mod, #tree{measured=V}) ->
  V;
measure(Mod, A) ->
  measure_len(Mod, A).

-spec add_measure(Mod :: module_name(), A :: term(), Acc :: measure()) -> measure().
add_measure(Mod, A, Acc) ->
  add_len(Mod, measure(Mod, A), Acc).

-spec measure_list(Mod :: module_name(), list()) -> measure().
measure_list(Mod, L) ->
  lists:foldl(fun(A, Acc) -> add_measure(Mod, A, Acc) end, null_len(Mod), L).

-spec cons(A :: term() | undefined, Acc :: list()) -> list().
cons(undefined, Acc) ->
  Acc;
cons(A, Acc) ->
  [A | Acc].

-spec make_node(Mod :: module_name(), Type :: atom(), List :: list()) -> #node{} | undefined.
make_node(_Mod, _Type, []) ->
  undefined; 
make_node(Mod, Type, List) ->
  #node{type=Type, measured=measure_list(Mod, List), list=List}.

-spec make_left_node(Mod :: module_name(), List :: list()) -> #node{type :: left_node}.
make_left_node(Mod, List) ->
  make_node(Mod, left_node, List).

-spec make_right_node(Mod :: module_name(), List :: list()) -> #node{type :: right_node}.
make_right_node(Mod, List) ->
  make_node(Mod, right_node, List).
   
-spec make_tree(Mod :: module_name(), 
                T :: #tree{}, 
                LeftNode :: #node{type :: left_node}, 
                TrunkDown :: #tree{}, 
                RightNode :: #node{type :: right_node}) -> #tree{}.
make_tree(Mod, T, LeftNode, TrunkDown, RightNode) ->
  LeftNode1 = get_left_node(LeftNode),
  RightNode1 = get_right_node(RightNode),
  T#tree{measured=measure_list(Mod, [LeftNode1, TrunkDown, RightNode1]),
         left_node=LeftNode1, trunk=TrunkDown, right_node=RightNode1}.

-spec get_right_node(Node :: #node{}) -> #node{type :: right_node}.
get_right_node(undefined) ->
  undefined;
get_right_node(#node{type=left_node, list=undefined} = Node) ->
  Node#node{type=right_node};
get_right_node(#node{type=left_node, list=List} = Node) ->
  Node#node{type=right_node, list=lists:reverse(List)};
get_right_node(#node{} = Node) ->
  Node.

-spec get_left_node(Node :: #node{}) -> #node{type :: left_node}.
get_left_node(undefined) ->
  undefined;
get_left_node(#node{type=right_node, list=undefined} = Node) ->
  Node#node{type=left_node};
get_left_node(#node{type=right_node, list=List} = Node) ->
  Node#node{type=left_node, list=lists:reverse(List)};
get_left_node(#node{} = Node) ->
  Node.

-spec make_split_node(Mod :: module_name(), 
                      Node :: #node{}, 
                      L1 :: list(), 
                      L2 :: list()) -> {#node{} | undefined, #node{} | undefined}.
make_split_node(Mod, #node{type = Type}, L1, L2) ->
  {make_node(Mod, Type, L1), make_node(Mod, Type, L2)}.

-spec split_node_at(Mod :: module_name(), 
                    SplitAt :: integer(), 
                    Node :: #node{}) -> {#node{} | undefined, #node{} | undefined}.
split_node_at(Mod, SplitAt, #node{list=List} = Node) ->
  {List1, List2} = lists:split(SplitAt, List),
  make_split_node(Mod, Node, List1, List2).

-spec split_node_fun(Mod :: module_name(), SplitPred :: fun()) -> fun().
split_node_fun(Mod, SplitPred) ->
  fun(A, {L1, L2, Init}) ->
    Init1 = add_len(Mod, measure_len(Mod, A), Init),
    case split_pred_len(SplitPred, Init1) of
      true  -> {[A | L1], L2, Init1};
      false -> {L1, [A | L2], Init1}
    end
  end.

-spec split_node(Mod :: module_name(), 
                 SplitPred :: fun(), 
                 Init :: measure(), 
                 Node :: #node{}) -> {#node{} | undefined, #node{} | undefined}.
split_node(Mod, SplitPred, Init,  #node{type=left_node, list = List} = Node) ->
  {List1, List2, _Init3} = lists:foldl(split_node_fun(Mod, SplitPred), {[], [], Init}, List),
  make_split_node(Mod, Node, lists:reverse(List1), lists:reverse(List2));
split_node(Mod, SplitPred, Init,  #node{type=right_node, list = List} = Node) ->
  {List1, List2, _Init3} = lists:foldl(split_node_fun(Mod, SplitPred), 
                                       {[], [], Init}, 
                                       lists:reverse(List)),
  make_split_node(Mod, Node, List1, List2).

-spec move_node_down_l(Mod :: module_name(), T :: #tree{}, Node :: #node{}) -> #tree{}.
move_node_down_l(_Mod, T, undefined) ->
  T;
move_node_down_l(Mod, #tree{left_node=undefined, trunk=undefined} = T, Node) ->
  make_tree(Mod, T, Node, T#tree.trunk, T#tree.right_node);
move_node_down_l(Mod, #tree{trunk=undefined, right_node=undefined} = T, Node) ->
  make_tree(Mod, T, Node, T#tree.trunk, T#tree.left_node);
move_node_down_l(Mod, #tree{trunk=undefined} = T, Node) ->
  T1 = make_tree(Mod, T, T#tree.left_node, undefined, undefined),
  make_tree(Mod, T, Node, T1, T#tree.right_node);
move_node_down_l(Mod, T, Node) ->
  T1 = move_node_down_l(Mod, T#tree.trunk, T#tree.left_node),
  make_tree(Mod, T, Node, T1, T#tree.right_node).

-spec move_list_down_l(Mod :: module_name(), T :: #tree{}, List :: list()) -> #tree{}.
move_list_down_l(Mod, T = #tree{}, List) ->
  lists:foldl(fun(A, Acc) -> move_node_down_l(Mod, Acc, A) end, T, List).

-spec move_node_down_r(Mod :: module_name(), T :: #tree{}, Node :: #node{}) -> #tree{}.
move_node_down_r(_Mod, T, undefined) ->
  T;
move_node_down_r(Mod, #tree{right_node=undefined, trunk=undefined} = T, Node) ->
  make_tree(Mod, T, T#tree.left_node, T#tree.trunk, Node);
move_node_down_r(Mod, #tree{left_node=undefined, trunk=undefined} = T, Node) ->
  make_tree(Mod, T, T#tree.right_node, T#tree.trunk, Node);
move_node_down_r(Mod, #tree{trunk=undefined} = T, Node) ->
  T1 = make_tree(Mod, T, undefined, undefined, T#tree.right_node),
  make_tree(Mod, T, T#tree.left_node, T1, Node);
move_node_down_r(Mod, T, Node) ->
  T1 = move_node_down_r(Mod, T#tree.trunk, T#tree.right_node),
  make_tree(Mod, T, T#tree.left_node, T1, Node).

-spec move_list_down_r(Mod :: module_name(), T :: #tree{}, List :: list()) -> #tree{}.
move_list_down_r(Mod, T = #tree{}, List) ->
  lists:foldl(fun(A, Acc) -> move_node_down_r(Mod, Acc, A) end, T, List).

-spec cons_l(Mod :: module_name(), A :: term(), T :: #tree{}) -> #tree{}.
cons_l(Mod, A, #tree{left_node=undefined} = T) ->
  make_tree(Mod, T, make_left_node(Mod, [A]), T#tree.trunk, T#tree.right_node);
cons_l(Mod, A, T) ->
  Node = make_left_node(Mod, [A | T#tree.left_node#node.list]),
  Len = len_node(Node),
  case Len > T#tree.node_size of
    true  -> {Node1, Node2} = split_node_at(Mod,
                                            split_list_at(T#tree.node_size, Len), 
                                            Node),
             T1 = make_tree(Mod, T, Node2, T#tree.trunk, T#tree.right_node),
             move_node_down_l(Mod, T1, Node1);
    false -> make_tree(Mod, T, Node, T#tree.trunk, T#tree.right_node)
  end.

-spec cons_r(Mod :: module_name(), A :: term(), T :: #tree{}) -> #tree{}.
cons_r(Mod, A, #tree{right_node=undefined} = T) ->
  make_tree(Mod, T, T#tree.left_node, T#tree.trunk, make_right_node(Mod, [A]));
cons_r(Mod, A, T) ->
  Node = make_right_node(Mod, [A | T#tree.right_node#node.list]),
  Len = len_node(Node),
  case Len > T#tree.node_size of
    true  -> {Node1, Node2} = split_node_at(Mod, 
                                            split_list_at(T#tree.node_size, Len), 
                                            Node),
             T1 = make_tree(Mod, T, T#tree.left_node, T#tree.trunk, Node2),
             move_node_down_r(Mod, T1, Node1);
    false -> make_tree(Mod, T, T#tree.left_node, T#tree.trunk, Node)
  end.

-spec move_node_up_l(Mod :: module_name(), T :: #tree{}) -> #tree{}.
move_node_up_l(_Mod, #tree{trunk=undefined, right_node=undefined}) ->
  undefined;
move_node_up_l(Mod, #tree{trunk=undefined} = T) ->
  make_tree(Mod, T, undefined, T#tree.trunk, T#tree.right_node);
move_node_up_l(Mod, #tree{trunk=TrunkDown} = T) 
  when TrunkDown#tree.left_node =:= undefined andalso 
       TrunkDown#tree.trunk =:= undefined ->
  make_tree(Mod, T, TrunkDown#tree.right_node, undefined, T#tree.right_node);
move_node_up_l(Mod, T) ->
  make_tree(Mod, 
            T, 
            T#tree.trunk#tree.left_node, 
            move_node_up_l(Mod, T#tree.trunk), 
            T#tree.right_node).

-spec uncons_l(Mod :: module_name(), 
               T :: #tree{}) -> {{value, term()}, #tree{}} | {empty, #tree{}}.
uncons_l(_Mod, #tree{left_node=undefined, trunk=undefined, right_node=undefined} = T) ->
  {empty, T};
uncons_l(Mod, #tree{left_node=undefined, trunk=undefined} = T) ->
  [X | Xs] = lists:reverse(T#tree.right_node#node.list),
  T1 = case length(Xs) =:= 0 of
         true  -> make_tree(Mod, T, T#tree.left_node, T#tree.trunk, undefined);
         false -> make_tree(Mod, 
                            T, 
                            T#tree.left_node, 
                            T#tree.trunk, 
                            make_right_node(Mod, lists:reverse(Xs)))
       end,
  {{value, X}, T1};
uncons_l(Mod, #tree{trunk=undefined} = T) ->
  [X | Xs] = T#tree.left_node#node.list,
  T1 = case length(Xs) =:= 0 of
         true  -> make_tree(Mod, T, undefined, T#tree.trunk, T#tree.right_node);
         false -> make_tree(Mod, T, make_left_node(Mod, Xs), T#tree.trunk, T#tree.right_node)
       end,
  {{value, X}, T1};
uncons_l(Mod, T) ->
  [X | Xs] = T#tree.left_node#node.list,
  T1 = case length(Xs) =:= 0 of
         true  -> move_node_up_l(Mod, T);
         false -> make_tree(Mod, T, make_left_node(Mod,	Xs), T#tree.trunk, T#tree.right_node)
       end,
  {{value, X}, T1}.

-spec move_node_up_r(Mod :: module_name(), T :: #tree{}) -> #tree{}.
move_node_up_r(_Mod, #tree{trunk=undefined, left_node=undefined}) ->
  undefined;
move_node_up_r(Mod, #tree{trunk=undefined} = T) ->
  make_tree(Mod, T, T#tree.left_node, T#tree.trunk, undefined);
move_node_up_r(Mod, #tree{trunk=TrunkDown} = T)
  when TrunkDown#tree.right_node =:= undefined andalso
       TrunkDown#tree.trunk =:= undefined ->
  make_tree(Mod, T, T#tree.left_node, undefined, TrunkDown#tree.left_node);
move_node_up_r(Mod, T) ->
  make_tree(Mod, 
            T, 
            T#tree.left_node, 
            move_node_up_r(Mod, T#tree.trunk), 
            T#tree.trunk#tree.right_node).

-spec uncons_r(Mod :: module_name(), 
               T :: #tree{}) -> {{value, term()}, #tree{}} | {empty, #tree{}}.
uncons_r(_Mod, #tree{left_node=undefined, trunk=undefined, right_node=undefined} = T) ->
  {empty, T};
uncons_r(Mod, #tree{right_node=undefined, trunk=undefined} = T) ->
  [X | Xs] = lists:reverse(T#tree.left_node#node.list),
  T1 = case length(Xs) =:= 0 of
         true  -> make_tree(Mod, T, undefined, T#tree.trunk, T#tree.right_node);
         false -> make_tree(Mod, 
                            T, 
                            make_left_node(Mod, lists:reverse(Xs)), 
                            T#tree.trunk, T#tree.right_node)
       end,
  {{value, X}, T1};
uncons_r(Mod, #tree{trunk=undefined} = T) ->
  [X | Xs] = T#tree.right_node#node.list,
  T1 = case length(Xs) =:= 0 of
         true  -> make_tree(Mod, T, T#tree.left_node, T#tree.trunk, undefined);
         false -> make_tree(Mod, T, T#tree.left_node, T#tree.trunk, make_right_node(Mod, Xs))
       end,
  {{value, X}, T1};
uncons_r(Mod, T) ->
  [X | Xs] = T#tree.right_node#node.list,
  T1 = case length(Xs) =:= 0 of
         true  -> move_node_up_r(Mod, T);
         false -> make_tree(Mod, T, T#tree.left_node, T#tree.trunk, make_right_node(Mod, Xs))
       end,
  {{value, X}, T1}.

-spec from_list_l(Mod :: module_name(), L :: list(), T :: #tree{}) -> #tree{}.
from_list_l(Mod, L, T) ->
  lists:foldl(fun(A, TA) -> cons_l(Mod, A, TA) end, T, L).

-spec from_list_r(Mod :: module_name(), L :: list(), T :: #tree{}) -> #tree{}.
from_list_r(Mod, L, T) ->
  lists:foldl(fun(A, TA) -> cons_r(Mod, A, TA) end, T, L).

-spec to_list_l(Arg :: #node{} | #tree{}, list()) -> list(). 
to_list_l(undefined, Acc) ->
  Acc;
to_list_l(#node{type=left_node, list=List}, Acc) ->
  lists:foldl(fun cons/2, Acc, List);
to_list_l(#node{type=right_node, list=List}, Acc) ->
  lists:foldl(fun cons/2, Acc, lists:reverse(List));
to_list_l(#tree{left_node=LeftNode, trunk=TrunkDown, right_node=RightNode}, Acc) ->
  Acc1 = to_list_l(LeftNode, Acc),
  Acc2 = to_list_l(TrunkDown, Acc1),
  to_list_l(RightNode, Acc2).  

-spec to_list_r(Arg :: #node{} | #tree{}, Acc :: list()) -> list().
to_list_r(undefined, Acc) ->
  Acc;
to_list_r(#node{type=right_node, list=List}, Acc) ->
  lists:foldl(fun cons/2, Acc, List);
to_list_r(#node{type=left_node, list=List}, Acc) ->
  lists:foldl(fun cons/2, Acc, lists:reverse(List));
to_list_r(#tree{left_node=LeftNode, trunk=TrunkDown, right_node=RightNode}, Acc) ->
  Acc1 = to_list_r(RightNode, Acc),
  Acc2 = to_list_r(TrunkDown, Acc1),
  to_list_r(LeftNode, Acc2).

-spec merge_node(Mod :: module_name(), 
                 T :: #tree{}, 
                 N1 :: #node{}, 
                 N2 :: #node{}) -> #node{} | {#node{}, #node{}} | undefined.
merge_node(_Mod, _T, N1, undefined) ->
  N1;
merge_node(_Mod, _T, undefined, N2) ->
  N2;
merge_node(Mod, T, N1, N2) ->
  case merge_required(T#tree.node_size, len_node(N1), len_node(N2)) of
    true  -> process_merge_node(Mod, T, N1, N2);
    false -> {N1, N2}
  end.

-spec process_merge_node(Mod :: module_name(), 
                         T :: #tree{}, 
                         N1 :: #node{}, 
                         N2 :: #node{}) -> #node{} | {#node{}, #node{}}.
process_merge_node(Mod, T, N1, N2) ->
  N3 = make_merged_node(Mod, N1, N2),
  case len_node(N3) >= (2*T#tree.node_size) of 
    true  -> split_node_at(Mod, (len_node(N3) div 2), N3); 
    false ->  N3
  end.

-spec make_merged_node(Mod :: module_name(), N1 :: #node{}, N2 :: #node{}) -> #node{}.
make_merged_node(Mod, #node{type=left_node} = N1, #node{type=left_node} = N2) ->
  make_node(Mod, left_node, (N1#node.list ++ N2#node.list));
make_merged_node(Mod, #node{type=left_node} = N1, #node{type=right_node} = N2) ->
  make_node(Mod, left_node, (N1#node.list ++ lists:reverse(N2#node.list)));
make_merged_node(Mod, #node{type=right_node} = N1, #node{type=left_node} = N2) ->
  make_node(Mod, left_node, (lists:reverse(N1#node.list) ++ N2#node.list));
make_merged_node(Mod, #node{type=right_node} = N1, #node{type=right_node} = N2) ->
  make_node(Mod, left_node, (lists:reverse(N1#node.list) ++ lists:reverse(N2#node.list))).

-spec process_fast_join(Mod :: module_name(), T1 :: #tree{}, T2 :: #tree{}) -> #tree{}.
process_fast_join(Mod, 
                  #tree{trunk=undefined, right_node=undefined} = T1, 
                  #tree{trunk=undefined, right_node=undefined} = T2) ->
  case merge_node(Mod, T1, T1#tree.left_node, T2#tree.left_node) of
    {N1, N2} -> make_tree(Mod, T1, N1, undefined, N2);
    N3       -> make_tree(Mod, T1, N3, undefined, undefined)
  end;
process_fast_join(Mod,
                  #tree{trunk=undefined, right_node=undefined} = T1,
                  #tree{trunk=undefined, left_node=undefined} = T2) ->
  case merge_node(Mod, T1, T1#tree.left_node, T2#tree.right_node) of
    {N1, N2} -> make_tree(Mod, T1, N1, undefined, N2);
    N3       -> make_tree(Mod, T1, N3, undefined, undefined)
  end;
process_fast_join(Mod,
                  #tree{trunk=undefined, left_node=undefined} = T1,
                  #tree{trunk=undefined, right_node=undefined} = T2) ->
  case merge_node(Mod, T1, T1#tree.right_node, T2#tree.left_node) of
    {N1, N2} -> make_tree(Mod, T1, N1, undefined, N2);
    N3       -> make_tree(Mod, T1, N3, undefined, undefined)
  end;
process_fast_join(Mod,
                  #tree{trunk=undefined, left_node=undefined} = T1,
                  #tree{trunk=undefined, left_node=undefined} = T2) ->
  case merge_node(Mod, T1, T1#tree.right_node, T2#tree.right_node) of
    {N1, N2} -> make_tree(Mod, T1, N1, undefined, N2);
    N3       -> make_tree(Mod, T1, N3, undefined, undefined)
  end;
process_fast_join(Mod,
                  #tree{trunk=undefined, right_node=undefined} = T1,
                  #tree{trunk=undefined} = T2) ->
  case merge_node(Mod, T1, T1#tree.left_node, T2#tree.left_node) of
    {N1, N2} -> T3 = make_tree(Mod, T1, N2, undefined, T2#tree.right_node),
                move_node_down_l(Mod, T3, N1);
    N3       -> make_tree(Mod, T1, N3, undefined, T2#tree.right_node)
  end;
process_fast_join(Mod,
                  #tree{trunk=undefined, left_node=undefined} = T1,
                  #tree{trunk=undefined} = T2) ->
  case merge_node(Mod, T1, T1#tree.right_node, T2#tree.left_node) of
    {N1, N2} -> T3 = make_tree(Mod, T1, N2, undefined, T2#tree.right_node),
                move_node_down_l(Mod, T3, N1);
    N3       -> make_tree(Mod, T1, N3, undefined, T2#tree.right_node)
  end;
process_fast_join(Mod,
                  #tree{trunk=undefined} = T1,
                  #tree{trunk=undefined, right_node=undefined} = T2) ->
  case merge_node(Mod, T1, T1#tree.right_node, T2#tree.left_node) of
    {N1, N2} -> T3 = make_tree(Mod, T1, T1#tree.left_node, undefined, N1),
                move_node_down_r(Mod, T3, N2);
    N3       -> make_tree(Mod, T1, T1#tree.left_node, undefined, N3)
  end;
process_fast_join(Mod,
                  #tree{trunk=undefined} = T1,
                  #tree{trunk=undefined, left_node=undefined} = T2) ->
  case merge_node(Mod, T1, T1#tree.right_node, T2#tree.right_node) of
    {N1, N2} -> T3 = make_tree(Mod, T1, T1#tree.left_node, undefined, N1),
                move_node_down_r(Mod, T3, N2);
    N3       -> make_tree(Mod, T1, T1#tree.left_node, undefined, N3)
  end;
process_fast_join(Mod,
                  #tree{trunk=undefined} = T1,
                  #tree{trunk=undefined} = T2) ->
  case merge_node(Mod, T1, T1#tree.right_node, T2#tree.left_node) of
    {N1, N2} -> T3 = make_tree(Mod, T2, N2, T2#tree.trunk, T2#tree.right_node),
                T4 = move_node_down_l(Mod, T3, N1),
                move_node_down_l(Mod, T4, T1#tree.left_node);
    N3       -> T3 = make_tree(Mod, T2, N3, T2#tree.trunk, T2#tree.right_node),
                move_node_down_l(Mod, T3, T1#tree.left_node)
  end;
process_fast_join(Mod, T1, T2) ->
  case {merge_node(Mod, T1, T1#tree.right_node, T2#tree.left_node), len(T1) < len(T2)} of
    {{N1, N2}, true}  -> T3 = make_tree(Mod, T2, N2, T2#tree.trunk, T2#tree.right_node),
                         T4 = move_node_down_l(Mod, T3, N1),
                         L4 = [T1#tree.left_node],
                         {T5, L5} = process_fast_join_l(Mod, T1#tree.trunk, {T4, L4}),
                         move_list_down_l(Mod, T5, L5);
    {{N1, N2}, false} -> T3 = make_tree(Mod, T1, T1#tree.left_node, T1#tree.trunk, N1),
                         T4 = move_node_down_r(Mod, T3, N2),
                         L4 = [T2#tree.right_node],
                         {T5, L5} = process_fast_join_r(Mod, T2#tree.trunk, {T4, L4}),
                         move_list_down_r(Mod, T5, L5);
    {N1, true}        -> T4 = make_tree(Mod, T2, N1, T2#tree.trunk, T2#tree.right_node),
                         L4 = [T1#tree.left_node],
                         {T5, L5} = process_fast_join_l(Mod, T1#tree.trunk, {T4, L4}),
                         move_list_down_l(Mod, T5, L5);
    {N1, false}       -> T4 = make_tree(Mod, T1, T1#tree.left_node, T1#tree.trunk, N1),
                         L4 = [T2#tree.right_node],
                         {T5, L5} = process_fast_join_r(Mod, T2#tree.trunk, {T4, L4}),
                         move_list_down_r(Mod, T5, L5)
  end.

-spec process_fast_join_l(Mod :: module_name(),
                          T1  :: #tree{},
                          {T2 :: #tree{}, L2 :: list()}) -> {#tree{}, list()}.
process_fast_join_l(Mod, #tree{trunk=undefined} = T1, {T2, L2}) ->
  {move_node_down_l(Mod, T2, T1#tree.right_node), cons(T1#tree.left_node, L2)};
process_fast_join_l(Mod, T1, {T2, L2}) ->
  {T3, L3} = {move_node_down_l(Mod, T2, T1#tree.right_node), cons(T1#tree.left_node, L2)},
  process_fast_join_l(Mod, T1#tree.trunk, {T3, L3}).

-spec process_fast_join_r(Mod :: module_name(),
			  T1  :: #tree{},
			  {T2 :: #tree{}, L2 ::	list()}) -> {#tree{}, list()}.
process_fast_join_r(Mod, #tree{trunk=undefined} = T1, {T2, L2}) ->
  {move_node_down_r(Mod, T2, T1#tree.left_node), cons(T1#tree.right_node, L2)};
process_fast_join_r(Mod, T1, {T2, L2}) ->
  {T3, L3} = {move_node_down_r(Mod, T2, T1#tree.left_node), cons(T1#tree.right_node, L2)},
  process_fast_join_r(Mod, T1#tree.trunk, {T3, L3}).

-spec fast_join(Mod :: module_name(), 
                T1 :: #tree{}, 
                T2 :: #tree{}) -> #tree{} | {error, not_similar_struc} | undefined.
fast_join(_Mod, T1, undefined) ->
  T1;
fast_join(_Mod, undefined, T2) ->
  T2;
fast_join(Mod, T1, T2) ->
  case is_similar(T1, T2) of
    true  -> process_fast_join(Mod, T1, T2);
    false -> {error, not_similar_struc}
  end.

-spec join_l(Mod :: module_name(), 
             T1 :: #tree{}, 
             T2 :: #tree{}) -> #tree{} | {error, not_similar_struc} | undefined.
join_l(_Mod, undefined, T2) ->
  T2;
join_l(_Mod, T1, undefined) ->
  T1;
join_l(Mod, T1, T2) ->
  case is_similar(T1, T2) of
    true  -> lists:foldl(fun(A, Acc) -> cons_l(Mod, A, Acc) end, T2, to_list_l(T1, []));
    false -> {error, not_similar_struc}
  end.

-spec join_r(Mod :: module_name(), 
             T1 :: #tree{}, 
             T2 :: #tree{}) -> #tree{} | {error, not_similar_struc} | undefined.
join_r(_Mod, undefined,	T2) ->
  T2;
join_r(_Mod, T1, undefined) ->
  T1;
join_r(Mod, T1, T2) ->
  case is_similar(T1, T2) of
    true  -> lists:foldl(fun(A, Acc) -> cons_r(Mod, A, Acc) end, T1, to_list_r(T2, []));
    false -> {error, not_similar_struc}
  end.

-spec join(Mod :: module_name(), 
           T1 :: #tree{}, 
           T2 :: #tree{}) -> #tree{} | {error, not_similar_struc} | undefined.
join(_Mod, undefined, T2) ->
  T2;
join(_Mod, T1, undefined) ->
  T1;
join(Mod, T1, T2) ->
  case is_similar(T1, T2) of 
    true  -> case {len(T1), len(T2)} of
               {0, _L2}              -> T2;
               {_L1, 0}              -> T1;
               {L1, L2} when L1 < L2 -> join_l(Mod, T1, T2);
               _                     -> join_r(Mod, T1, T2)
             end;
    false -> {error, not_similar_struc}
  end.

-spec merge_split_list(Mod :: module_name(), 
                       {{TL :: #tree{}, LL :: list()}, 
                        {TR :: #tree{}, LR :: list()}}) -> {#tree{}, #tree{}}.
merge_split_list(Mod, {{TL, LL}, {TR, LR}}) ->
  TL1 = move_list_down_r(Mod, TL, LL),
  TR1 = move_list_down_l(Mod, TR, LR),
  {TL1, TR1}.
  
-spec split(Mod :: module_name(), SplitPred :: fun(), T :: #tree{}) -> {#tree{}, #tree{}}.
split(Mod, SplitPred, T) ->
  {{TL, LL}, {TR, LR}} = split_acc(Mod, 
                                   SplitPred, 
                                   T, 
                                   null_len(Mod), 
                                   {{new(T#tree.type, 
                                         T#tree.node_size, 
                                         T#tree.attribute), []}, 
                                    {new(T#tree.type, 
                                         T#tree.node_size, 
                                         T#tree.attribute), []}}),
  merge_split_list(Mod, {{TL, LL}, {TR, LR}}).

-spec split_acc(Mod :: module_name(), 
                SplitPred :: fun(), 
                T :: #tree{}, 
                Init :: measure(), 
                {{TL :: #tree{}, 
                  LL :: list()}, 
                 {TR :: #tree{}, 
                  LR :: list()}}) -> {{#tree{}, list()}, {#tree{}, list()}}.
split_acc(_Mod, 
          _SplitPred, 
          #tree{left_node=undefined, trunk=undefined, right_node=undefined}, 
          _Init, 
          {{TL, LL}, {TR, LR}}) ->
  {{TL, LL}, {TR, LR}};
split_acc(Mod, 
          SplitPred, 
          #tree{left_node=undefined, trunk=undefined} = T, 
          Init, 
          {{TL, LL}, {TR, LR}}) ->
  process_split_node(Mod, 
                     SplitPred, 
                     T#tree.right_node, 
                     Init, 
                     {{TL, LL}, {TR, LR}}); 
split_acc(Mod, 
          SplitPred, 
          #tree{trunk=undefined, right_node=undefined} = T, 
          Init, 
          {{TL, LL}, {TR, LR}}) ->
  process_split_node(Mod, 
                     SplitPred, 
                     T#tree.left_node,	 
                     Init, 
                     {{TL, LL}, {TR, LR}});
split_acc(Mod, 
          SplitPred, 
          #tree{trunk=undefined} = T, 
          Init, 
          {{TL, LL}, {TR, LR}}) ->
  Init1 = add_len(Mod, T#tree.left_node#node.measured, Init),
  {{TL1, LL1}, {TR1, LR1}} = process_split_node(Mod, 
                                                SplitPred, 
                                                T#tree.left_node, 
                                                Init, 
                                                {{TL, LL}, {TR, LR}}),
  process_split_node(Mod, 
                     SplitPred, 
                     T#tree.right_node, 
                     Init1, 
                     {{TL1, LL1}, {TR1, LR1}});
split_acc(Mod, SplitPred, T, Init, {{TL, LL}, {TR, LR}}) ->
  Init1 = add_len(Mod, T#tree.left_node#node.measured, Init),
  Init2 = add_len(Mod, T#tree.trunk#tree.measured, Init1),
  {{TL1, LL1}, {TR1, LR1}} = process_split_node(Mod, 
                                                SplitPred, 
                                                T#tree.left_node, 
                                                Init, 
                                                {{TL, LL}, {TR, LR}}),
  {{TL2, LL2}, {TR2, LR2}} = process_split_node(Mod, 
                                                SplitPred, 
                                                T#tree.right_node, 
                                                Init2, 
                                                {{TL1, LL1}, {TR1, LR1}}),
  split_acc(Mod, SplitPred, T#tree.trunk, Init1, {{TL2, LL2}, {TR2, LR2}}).

-spec process_split_node(Mod :: module_name(), 
                         SplitPred :: fun(), 
                         Node :: #node{}, 
                         Init :: measure(), 
                         {{TL :: #tree{}, 
                           LL :: list()}, 
                          {TR :: #tree{}, 
                           LR :: list()}}) -> {{#tree{}, list()}, {#tree{}, list()}}. 
process_split_node(Mod, SplitPred, #node{type=left_node} = Node, Init, {{TL, LL}, {TR, LR}}) ->
  {N1, N2} = split_node(Mod, SplitPred, Init, Node),
  TL1 = move_node_down_r(Mod, TL, N1),
  {{TL1, LL}, {TR, cons(N2, LR)}};
process_split_node(Mod, SplitPred, #node{type=right_node} = Node, Init, {{TL, LL}, {TR, LR}}) ->
  {N1, N2} = split_node(Mod, SplitPred, Init, Node),
  TR1 = move_node_down_l(Mod, TR, N2),
  {{TL, cons(N1, LL)}, {TR1, LR}}.










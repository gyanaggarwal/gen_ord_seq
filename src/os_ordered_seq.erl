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

-module(os_ordered_seq).
-author("gyanendra aggarwal").

-behavior(gen_ord_seq).

-export([new_seq/1, new_useq/1, new_map/1, new_umap/1, len/1, is_member/2, 
         merge/2, 
         to_list/1, from_list_seq/2, from_list_map/2, from_list_useq/2, from_list_umap/2, app_from_list/2,
         insert/2, insert/3, delete/2, get/2, take/2, take_max/1, take_min/1]).

-export([measure/1, null/0, add/2]).

-define(TYPE, ?MODULE).

-type os_ordered_seq() :: term().
-type os_ordered_map() :: term().
-type os_ordered_struc() :: os_ordered_seq() | os_ordered_map().

-spec is_osmap(T :: os_ordered_struc()) -> true | false.
is_osmap(T) ->
  case gen_ord_seq:get_attribute(T) of
    {_, map} -> true;
    _        -> false
  end.

-spec is_osunique(T :: os_ordered_struc()) -> true | false.
is_osunique(T) ->
  case gen_ord_seq:get_attribute(T) of 
    {unique, _} -> true;
    _           -> false
  end.

-spec get_key(K :: {term(), term()} | term()) -> term().
get_key({K, _V}) ->
  K;
get_key(K) ->
  K.

-spec new(NodeSize :: integer(), Attribute :: term()) -> os_ordered_struc().
new(NodeSize, Attribute) ->
  gen_ord_seq:new(?TYPE, NodeSize, Attribute).

-spec new_seq(NodeSize :: integer()) -> os_ordered_seq().
new_seq(NodeSize) ->
  new(NodeSize, {non_unique, seq}).

-spec new_useq(NodeSize :: integer()) -> os_ordered_seq().
new_useq(NodeSize) ->
  new(NodeSize, {unique, seq}).

-spec new_map(NodeSize :: integer()) -> os_ordered_map().
new_map(NodeSize) ->
  new(NodeSize, {non_unique, map}).

-spec new_umap(NodeSize :: integer()) -> os_ordered_map().
new_umap(NodeSize) ->
  new(NodeSize, {unique, map}).

-spec len(T :: os_ordered_struc()) -> integer().
len(T) ->
  gen_ord_seq:len(T).

-spec split(Fun :: fun(), K :: term(), T :: os_ordered_struc()) -> {os_ordered_struc(), os_ordered_struc()}.
split(Fun, K, T) ->
  gen_ord_seq:split(?MODULE, gen_ord_seq:pred_fun(Fun, get_key(K)), T).

-spec split_less_than(K :: term(), T :: os_ordered_struc()) -> {os_ordered_struc(), os_ordered_struc()}.
split_less_than(K, T) ->
  split(fun erlang:'<'/2, K, T).

-spec split(K :: term(), T :: os_ordered_struc()) -> {os_ordered_struc(), os_ordered_struc()}.
split(K, T) ->
  split(fun erlang:'=<'/2, K, T).

-spec join(T1 :: os_ordered_struc(), T2 :: os_ordered_struc()) -> os_ordered_struc().
join(T1, T2) ->
  gen_ord_seq:join(?MODULE, T1, T2).

-spec is_member(K :: term(), T :: os_ordered_struc()) -> true | false.
is_member(K, T) ->
  {L, _R} = split(K, T),
  case gen_ord_seq:uncons_r(?MODULE, L) of
    {{value, {K, _}}, _} -> true;
    {{value, K}, _}      -> true;
    _                    -> false
  end.

-spec insert(K :: term(), V :: term(), T :: os_ordered_struc()) -> os_ordered_struc().
insert(K, V, T) ->
  K1 = case is_osmap(T) of
         true  -> {K, V};
         false -> K
       end,
  insert(K1, T).

-spec insert(K :: term(), T :: os_ordered_struc()) -> os_ordered_struc().
insert(K, T) ->
  insert1(K, T, true).

-spec insert1(K :: term(), T :: os_ordered_struc(), U :: true | false) -> os_ordered_struc().
insert1(K, T, U) ->
  case len(T) =:= 0 of
    true  -> gen_ord_seq:cons_l(?MODULE, K, T);
    false -> {T1, T2} = split(K, T),
             T9 = case is_osunique(T) of
                    true  -> {T3, T4} = split_less_than(K, T1),
                             case {U, len(T4)} of
                               {true, _}  -> {T3, T2};
                               {false, 0} -> {T3, T2};
                               {false, _} -> T
                             end;
                    false -> {T1, T2}
                  end,
             case T9 of
               {T5, T6} -> {T7, T8} = case len(T5) < len(T6) of
                                        true  -> {T5, gen_ord_seq:cons_l(?MODULE, K, T6)};
                                        false -> {gen_ord_seq:cons_r(?MODULE, K, T5), T6}
                                      end,
                           join(T7, T8);
               _        -> T9
            end
  end.

-spec take_min(T :: os_ordered_struc()) -> {{value, term()} | empty, os_ordered_struc()}.
take_min(T) ->
  gen_ord_seq:uncons_l(?MODULE, T).

-spec take_max(T :: os_ordered_struc()) -> {{value, term()} | empty, os_ordered_struc()}.
take_max(T) ->
  gen_ord_seq:uncons_r(?MODULE, T).

-spec split_delete(K :: term(), T :: os_ordered_struc()) -> {{os_ordered_struc(), os_ordered_struc()}, {os_ordered_struc(), os_ordered_struc()}}.
split_delete(K, T) ->
  {L, R} = split(K, T),
  {L1, R1} = split_less_than(K, L),
  {{L, R}, {L1, R1}}.

-spec take(K :: term(), T :: os_ordered_struc()) -> {{value, list()}, os_ordered_struc()}.
take(K, T) ->
  {{_L, R}, {L1, R1}} = split_delete(K, T),
  {{value, to_list(R1)}, join(L1, R)}.
  
-spec delete(K :: term(), T :: os_ordered_struc()) -> os_ordered_struc().
delete(K, T) ->
  {{_L, R}, {L1, R1}} = split_delete(K, T),
  case len(R1) =:= 0 of
    true  -> T;
    false -> join(L1, R)
  end.

-spec get(K :: term(), T :: os_ordered_struc()) -> {value, list()}.
get(K, T) ->
  {{_L, _R}, {_L1, R1}} = split_delete(K, T),
  {value, to_list(R1)}.

-spec app_from_list(L :: list(), T :: os_ordered_struc()) -> os_ordered_struc().
app_from_list(L, T) ->
  app_from_list(L, T, true).

-spec app_from_list(L :: list(), T :: os_ordered_struc(), U :: true | false) -> os_ordered_struc().
app_from_list(L, T, U) ->
  lists:foldl(fun(A, Acc) -> insert1(A, Acc, U) end, T, L).

-spec from_list_seq(Size :: integer(), L :: list()) -> os_ordered_seq().
from_list_seq(Size, L) ->
  app_from_list(L, new_seq(Size)).

-spec from_list_map(Size :: integer(), L :: list()) -> os_ordered_map().
from_list_map(Size, L) ->
  app_from_list(L, new_map(Size)).

-spec from_list_useq(Size :: integer(), L :: list()) -> os_ordered_seq().
from_list_useq(Size, L) ->
  app_from_list(L, new_useq(Size)).

-spec from_list_umap(Size :: integer(), L :: list()) -> os_ordered_map().
from_list_umap(Size, L) ->
  app_from_list(L, new_umap(Size)).

-spec to_list(T :: os_ordered_struc()) -> list().
to_list(T) ->
  gen_ord_seq:to_list_r(T, []).

-spec merge(T1 :: os_ordered_struc() | undefined, T2 :: os_ordered_struc() | undefined) -> os_ordered_struc() | {error, not_similar_struc} | undefined.
merge(undefined, undefined) ->
  undefined;
merge(undefined, T2) ->
  T2;
merge(T1, undefined) ->
  T1;
merge(T1, T2) ->
  case gen_ord_seq:is_similar(T1, T2) of
    true  -> case len(T1) < len(T2) of
               true  -> app_from_list(to_list(T1), T2, true);
               false -> app_from_list(to_list(T2), T1, false)
             end;
    false -> {error, not_similar_struc}
  end.

-spec measure(Arg :: {term(), term()} | term()) -> term().
measure({K, _V}) ->
  K;
measure(K) ->
  K.

-spec null() -> undefined.
null()     ->
  undefined.

-spec add(Max1 :: term(), Max2 :: term()) -> term().
add(undefined, Max) ->
  Max;
add(Max, undefined) ->
  Max;
add(Max1, Max2) when Max1 =< Max2 ->
  Max2;
add(Max1, _Max2) ->
  Max1.


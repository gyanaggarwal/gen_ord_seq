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

-module(os_priority_queue).
-author("gyanendra aggarwal").

-behavior(gen_ord_seq).

-export([new/1, len/1, to_list/1, insert/3, take/1]).

-export([measure/1, null/0, add/2]).

-define(TYPE, ?MODULE).

-type os_priority_queue() :: term().

-spec new(NodeSize :: integer()) -> os_priority_queue().
new(NodeSize) ->
  gen_ord_seq:new(?TYPE, NodeSize, {non_unique, map}).

-spec len(Q :: os_priority_queue()) -> integer().
len(Q) ->
  gen_ord_seq:len(Q).

-spec to_list(Q :: os_priority_queue()) -> list().
to_list(Q) ->
  gen_ord_seq:to_list_l(Q, []).

-spec take(Q :: os_priority_queue()) -> {{value, {term(), term()}} | empty, os_priority_queue()}.
take(Q) ->
  gen_ord_seq:uncons_r(?MODULE, Q).

-spec insert(Pri :: term(), V :: term(), Q :: os_priority_queue()) -> os_priority_queue().
insert(Pri, V, Q) ->
  {L, R} = gen_ord_seq:split(?MODULE, gen_ord_seq:pred_fun(fun erlang:'<'/2, Pri), Q),
  gen_ord_seq:join(?MODULE, L, gen_ord_seq:cons_l(?MODULE, {Pri, V}, R)).

-spec measure({Pri :: term(), V :: term()}) -> term().
measure({Pri, _V}) ->
  Pri.

-spec null() -> undefined.
null() ->
  undefined.

-spec add(Pri1 :: term(), Pri2 :: term()) -> term().
add(Pri, undefined) ->
  Pri;
add(undefined, Pri) ->
  Pri;
add(Pri1, Pri2) when Pri1 =< Pri2 ->
  Pri2;
add(Pri1, _Pri2) ->
  Pri1.


%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:22 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   22 (  22 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (27346)Refutation not found, incomplete strategy% (27346)------------------------------
% (27346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27346)Termination reason: Refutation not found, incomplete strategy

tff(u55,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) )).

% (27346)Memory used [KB]: 9850
tff(u54,negated_conjecture,
    ( ~ ~ r2_hidden(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,u1_struct_0(sK1)) )).

tff(u53,negated_conjecture,(
    ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

% (27346)Time elapsed: 0.071 s
tff(u52,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) )).

% (27346)------------------------------
% (27346)------------------------------
tff(u51,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u50,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u49,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) )).

tff(u48,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u47,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u46,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) )).

tff(u45,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u44,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u43,negated_conjecture,(
    l1_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (27348)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.20/0.50  % (27346)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.20/0.50  % (27344)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.50  % (27344)# SZS output start Saturation.
% 0.20/0.50  % (27346)Refutation not found, incomplete strategy% (27346)------------------------------
% 0.20/0.50  % (27346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27346)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  tff(u55,axiom,
% 0.20/0.50      (![X1, X0] : ((~r2_hidden(X0,X1) | m1_subset_1(X0,X1))))).
% 0.20/0.50  
% 0.20/0.50  % (27346)Memory used [KB]: 9850
% 0.20/0.50  tff(u54,negated_conjecture,
% 0.20/0.50      ((~~r2_hidden(sK2,u1_struct_0(sK1))) | ~r2_hidden(sK2,u1_struct_0(sK1)))).
% 0.20/0.50  
% 0.20/0.50  tff(u53,negated_conjecture,
% 0.20/0.50      ~m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.50  
% 0.20/0.50  % (27346)Time elapsed: 0.071 s
% 0.20/0.50  tff(u52,axiom,
% 0.20/0.50      (![X1, X0] : ((~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))))).
% 0.20/0.50  
% 0.20/0.50  % (27346)------------------------------
% 0.20/0.50  % (27346)------------------------------
% 0.20/0.50  tff(u51,negated_conjecture,
% 0.20/0.50      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.20/0.50  
% 0.20/0.50  tff(u50,axiom,
% 0.20/0.50      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u49,negated_conjecture,
% 0.20/0.50      ((~v1_xboole_0(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK1)))).
% 0.20/0.50  
% 0.20/0.50  tff(u48,negated_conjecture,
% 0.20/0.50      ~v2_struct_0(sK0)).
% 0.20/0.50  
% 0.20/0.50  tff(u47,negated_conjecture,
% 0.20/0.50      ~v2_struct_0(sK1)).
% 0.20/0.50  
% 0.20/0.50  tff(u46,negated_conjecture,
% 0.20/0.50      ((~v1_xboole_0(u1_struct_0(sK1))) | ~l1_struct_0(sK1))).
% 0.20/0.50  
% 0.20/0.50  tff(u45,negated_conjecture,
% 0.20/0.50      l1_struct_0(sK0)).
% 0.20/0.50  
% 0.20/0.50  tff(u44,axiom,
% 0.20/0.50      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u43,negated_conjecture,
% 0.20/0.50      l1_orders_2(sK0)).
% 0.20/0.50  
% 0.20/0.50  % (27344)# SZS output end Saturation.
% 0.20/0.50  % (27344)------------------------------
% 0.20/0.50  % (27344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27344)Termination reason: Satisfiable
% 0.20/0.50  
% 0.20/0.50  % (27344)Memory used [KB]: 5373
% 0.20/0.50  % (27344)Time elapsed: 0.096 s
% 0.20/0.50  % (27344)------------------------------
% 0.20/0.50  % (27344)------------------------------
% 0.20/0.50  % (27336)Success in time 0.152 s
%------------------------------------------------------------------------------

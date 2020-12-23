%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:21 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    0
%              Number of atoms          :   29 (  29 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u62,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u61,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK1))
    | r2_hidden(sK2,u1_struct_0(sK1)) )).

tff(u60,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u59,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK1)) )).

tff(u58,negated_conjecture,
    ( ~ ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK2) )).

tff(u57,negated_conjecture,(
    ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u56,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u55,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) )).

tff(u54,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u53,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) )).

tff(u52,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u51,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u50,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u49,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u48,negated_conjecture,(
    l1_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.47  % (2838)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.47  % (2838)# SZS output start Saturation.
% 0.22/0.47  tff(u62,axiom,
% 0.22/0.47      (![X1, X0] : ((~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0))))).
% 0.22/0.47  
% 0.22/0.47  tff(u61,negated_conjecture,
% 0.22/0.47      ((~~v1_xboole_0(u1_struct_0(sK1))) | r2_hidden(sK2,u1_struct_0(sK1)))).
% 0.22/0.47  
% 0.22/0.47  tff(u60,axiom,
% 0.22/0.47      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.22/0.47  
% 0.22/0.47  tff(u59,negated_conjecture,
% 0.22/0.47      ((~~v1_xboole_0(u1_struct_0(sK1))) | ~v1_xboole_0(u1_struct_0(sK1)))).
% 0.22/0.47  
% 0.22/0.47  tff(u58,negated_conjecture,
% 0.22/0.47      ((~~v1_xboole_0(sK2)) | ~v1_xboole_0(sK2))).
% 0.22/0.47  
% 0.22/0.47  tff(u57,negated_conjecture,
% 0.22/0.47      ~m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.22/0.47  
% 0.22/0.47  tff(u56,axiom,
% 0.22/0.47      (![X1, X0] : ((~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0))))).
% 0.22/0.47  
% 0.22/0.47  tff(u55,axiom,
% 0.22/0.47      (![X1, X0] : ((~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0))))).
% 0.22/0.47  
% 0.22/0.47  tff(u54,negated_conjecture,
% 0.22/0.47      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.22/0.47  
% 0.22/0.47  tff(u53,axiom,
% 0.22/0.47      (![X1, X0] : ((m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0))))).
% 0.22/0.47  
% 0.22/0.47  tff(u52,negated_conjecture,
% 0.22/0.47      ~v2_struct_0(sK0)).
% 0.22/0.47  
% 0.22/0.47  tff(u51,negated_conjecture,
% 0.22/0.47      ~v2_struct_0(sK1)).
% 0.22/0.47  
% 0.22/0.47  tff(u50,negated_conjecture,
% 0.22/0.47      l1_struct_0(sK0)).
% 0.22/0.47  
% 0.22/0.47  tff(u49,axiom,
% 0.22/0.47      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.22/0.47  
% 0.22/0.47  tff(u48,negated_conjecture,
% 0.22/0.47      l1_orders_2(sK0)).
% 0.22/0.47  
% 0.22/0.47  % (2838)# SZS output end Saturation.
% 0.22/0.47  % (2838)------------------------------
% 0.22/0.47  % (2838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (2838)Termination reason: Satisfiable
% 0.22/0.47  
% 0.22/0.47  % (2838)Memory used [KB]: 5373
% 0.22/0.47  % (2838)Time elapsed: 0.055 s
% 0.22/0.47  % (2838)------------------------------
% 0.22/0.47  % (2838)------------------------------
% 0.22/0.47  % (2830)Success in time 0.116 s
%------------------------------------------------------------------------------

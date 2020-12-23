%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:08 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :    8 (   8 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    0
%              Number of atoms          :   18 (  18 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u70,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k2_tarski(sK1,sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

tff(u69,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u68,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u67,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u66,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u65,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u64,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) )).

tff(u63,negated_conjecture,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK1,u1_struct_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.40  % (5967)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (5960)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.46  % (5967)# SZS output start Saturation.
% 0.20/0.46  tff(u70,negated_conjecture,
% 0.20/0.46      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)))).
% 0.20/0.46  
% 0.20/0.46  tff(u69,negated_conjecture,
% 0.20/0.46      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.20/0.46  
% 0.20/0.46  tff(u68,negated_conjecture,
% 0.20/0.46      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.20/0.46  
% 0.20/0.46  tff(u67,axiom,
% 0.20/0.46      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u66,axiom,
% 0.20/0.46      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u65,negated_conjecture,
% 0.20/0.46      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.20/0.46  
% 0.20/0.46  tff(u64,axiom,
% 0.20/0.46      (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k2_tarski(X1,X1)) | v1_xboole_0(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u63,negated_conjecture,
% 0.20/0.46      ((~m1_subset_1(sK1,u1_struct_0(sK0))) | m1_subset_1(sK1,u1_struct_0(sK0)))).
% 0.20/0.46  
% 0.20/0.46  % (5967)# SZS output end Saturation.
% 0.20/0.46  % (5967)------------------------------
% 0.20/0.46  % (5967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (5967)Termination reason: Satisfiable
% 0.20/0.46  
% 0.20/0.46  % (5967)Memory used [KB]: 6140
% 0.20/0.46  % (5967)Time elapsed: 0.057 s
% 0.20/0.46  % (5967)------------------------------
% 0.20/0.46  % (5967)------------------------------
% 0.20/0.46  % (5960)Refutation not found, incomplete strategy% (5960)------------------------------
% 0.20/0.46  % (5960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (5960)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (5960)Memory used [KB]: 1535
% 0.20/0.46  % (5960)Time elapsed: 0.051 s
% 0.20/0.46  % (5960)------------------------------
% 0.20/0.46  % (5960)------------------------------
% 0.20/0.46  % (5956)Success in time 0.111 s
%------------------------------------------------------------------------------

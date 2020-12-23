%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:13 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    0
%              Number of atoms          :   35 (  35 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u126,negated_conjecture,
    ( ~ ( sK1 != k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    | sK1 != k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

tff(u125,negated_conjecture,
    ( ~ ( sK1 != k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    | sK1 != k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

tff(u124,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) )).

tff(u123,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u122,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u121,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u120,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u119,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u118,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u117,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
      | v1_xboole_0(X0) ) )).

tff(u116,negated_conjecture,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u115,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | v3_orders_2(sK0) )).

tff(u114,axiom,(
    ! [X1,X0] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u113,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | r1_orders_2(sK0,sK1,sK1) )).

tff(u112,negated_conjecture,
    ( ~ v5_orders_2(sK0)
    | v5_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:38:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (3846)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.41  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.42  % (3846)# SZS output start Saturation.
% 0.21/0.42  tff(u126,negated_conjecture,
% 0.21/0.42      ((~(sK1 != k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) | (sK1 != k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))))).
% 0.21/0.42  
% 0.21/0.42  tff(u125,negated_conjecture,
% 0.21/0.42      ((~(sK1 != k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) | (sK1 != k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))))).
% 0.21/0.42  
% 0.21/0.42  tff(u124,negated_conjecture,
% 0.21/0.42      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))).
% 0.21/0.42  
% 0.21/0.42  tff(u123,negated_conjecture,
% 0.21/0.42      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.21/0.42  
% 0.21/0.42  tff(u122,negated_conjecture,
% 0.21/0.42      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.21/0.42  
% 0.21/0.42  tff(u121,axiom,
% 0.21/0.42      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.21/0.42  
% 0.21/0.42  tff(u120,negated_conjecture,
% 0.21/0.42      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.21/0.42  
% 0.21/0.42  tff(u119,axiom,
% 0.21/0.42      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.21/0.42  
% 0.21/0.42  tff(u118,negated_conjecture,
% 0.21/0.42      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.21/0.42  
% 0.21/0.42  tff(u117,axiom,
% 0.21/0.42      (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | v1_xboole_0(X0))))).
% 0.21/0.42  
% 0.21/0.42  tff(u116,negated_conjecture,
% 0.21/0.42      ((~m1_subset_1(sK1,u1_struct_0(sK0))) | m1_subset_1(sK1,u1_struct_0(sK0)))).
% 0.21/0.42  
% 0.21/0.42  tff(u115,negated_conjecture,
% 0.21/0.42      ((~v3_orders_2(sK0)) | v3_orders_2(sK0))).
% 0.21/0.42  
% 0.21/0.42  tff(u114,axiom,
% 0.21/0.42      (![X1, X0] : ((r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.42  
% 0.21/0.42  tff(u113,negated_conjecture,
% 0.21/0.42      ((~r1_orders_2(sK0,sK1,sK1)) | r1_orders_2(sK0,sK1,sK1))).
% 0.21/0.42  
% 0.21/0.42  tff(u112,negated_conjecture,
% 0.21/0.42      ((~v5_orders_2(sK0)) | v5_orders_2(sK0))).
% 0.21/0.42  
% 0.21/0.42  % (3846)# SZS output end Saturation.
% 0.21/0.42  % (3846)------------------------------
% 0.21/0.42  % (3846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (3846)Termination reason: Satisfiable
% 0.21/0.42  
% 0.21/0.42  % (3846)Memory used [KB]: 6140
% 0.21/0.42  % (3846)Time elapsed: 0.025 s
% 0.21/0.42  % (3846)------------------------------
% 0.21/0.42  % (3846)------------------------------
% 0.21/0.42  % (3839)Success in time 0.067 s
%------------------------------------------------------------------------------

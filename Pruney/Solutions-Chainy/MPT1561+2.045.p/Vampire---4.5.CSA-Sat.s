%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:13 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :    9 (   9 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    0
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u92,negated_conjecture,
    ( ~ ( sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1)) )
    | sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

tff(u91,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k2_tarski(sK1,sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

tff(u90,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u89,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u88,axiom,
    ( ~ ! [X0] :
          ( ~ v1_xboole_0(u1_struct_0(X0))
          | ~ l1_struct_0(X0)
          | v2_struct_0(X0) )
    | ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) )).

tff(u87,axiom,
    ( ~ ! [X0] :
          ( ~ l1_orders_2(X0)
          | l1_struct_0(X0) )
    | ! [X0] :
        ( ~ l1_orders_2(X0)
        | l1_struct_0(X0) ) )).

tff(u86,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u85,axiom,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(X1,X0)
          | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
          | v1_xboole_0(X0) )
    | ! [X1,X0] :
        ( ~ m1_subset_1(X1,X0)
        | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
        | v1_xboole_0(X0) ) )).

tff(u84,negated_conjecture,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK1,u1_struct_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:20:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.44  % (1687)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.44  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.44  % (1687)# SZS output start Saturation.
% 0.20/0.44  tff(u92,negated_conjecture,
% 0.20/0.44      ((~(sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1)))) | (sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1))))).
% 0.20/0.44  
% 0.20/0.44  tff(u91,negated_conjecture,
% 0.20/0.44      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)))).
% 0.20/0.44  
% 0.20/0.44  tff(u90,negated_conjecture,
% 0.20/0.44      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.20/0.44  
% 0.20/0.44  tff(u89,negated_conjecture,
% 0.20/0.44      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.20/0.44  
% 0.20/0.44  tff(u88,axiom,
% 0.20/0.44      ((~(![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))) | (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)))))).
% 0.20/0.44  
% 0.20/0.44  tff(u87,axiom,
% 0.20/0.44      ((~(![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))) | (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0)))))).
% 0.20/0.44  
% 0.20/0.44  tff(u86,negated_conjecture,
% 0.20/0.44      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.20/0.44  
% 0.20/0.44  tff(u85,axiom,
% 0.20/0.44      ((~(![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k2_tarski(X1,X1)) | v1_xboole_0(X0))))) | (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k2_tarski(X1,X1)) | v1_xboole_0(X0)))))).
% 0.20/0.44  
% 0.20/0.44  tff(u84,negated_conjecture,
% 0.20/0.44      ((~m1_subset_1(sK1,u1_struct_0(sK0))) | m1_subset_1(sK1,u1_struct_0(sK0)))).
% 0.20/0.44  
% 0.20/0.44  % (1687)# SZS output end Saturation.
% 0.20/0.44  % (1687)------------------------------
% 0.20/0.44  % (1687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (1687)Termination reason: Satisfiable
% 0.20/0.44  
% 0.20/0.44  % (1687)Memory used [KB]: 6140
% 0.20/0.44  % (1687)Time elapsed: 0.027 s
% 0.20/0.44  % (1687)------------------------------
% 0.20/0.44  % (1687)------------------------------
% 0.20/0.44  % (1679)Success in time 0.081 s
%------------------------------------------------------------------------------

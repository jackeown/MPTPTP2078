%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:11 EST 2020

% Result     : CounterSatisfiable 0.17s
% Output     : Saturation 0.17s
% Verified   : 
% Statistics : Number of formulae       :    9 (   9 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    0
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u60,negated_conjecture,
    ( ~ ( sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1)) )
    | sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

tff(u59,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k2_tarski(sK1,sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

tff(u58,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u57,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u56,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u55,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u54,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u53,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) )).

tff(u52,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.10  % Command    : run_vampire %s %d
% 0.10/0.30  % Computer   : n003.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 16:48:27 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.17/0.39  % (6694)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.17/0.40  % SZS status CounterSatisfiable for theBenchmark
% 0.17/0.40  % (6694)# SZS output start Saturation.
% 0.17/0.40  tff(u60,negated_conjecture,
% 0.17/0.40      ((~(sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1)))) | (sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1))))).
% 0.17/0.40  
% 0.17/0.40  tff(u59,negated_conjecture,
% 0.17/0.40      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)))).
% 0.17/0.40  
% 0.17/0.40  tff(u58,negated_conjecture,
% 0.17/0.40      ~v2_struct_0(sK0)).
% 0.17/0.40  
% 0.17/0.40  tff(u57,negated_conjecture,
% 0.17/0.40      l1_struct_0(sK0)).
% 0.17/0.40  
% 0.17/0.40  tff(u56,axiom,
% 0.17/0.40      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.17/0.40  
% 0.17/0.40  tff(u55,axiom,
% 0.17/0.40      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.17/0.40  
% 0.17/0.40  tff(u54,negated_conjecture,
% 0.17/0.40      l1_orders_2(sK0)).
% 0.17/0.40  
% 0.17/0.40  tff(u53,axiom,
% 0.17/0.40      (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k2_tarski(X1,X1)) | v1_xboole_0(X0))))).
% 0.17/0.40  
% 0.17/0.40  tff(u52,negated_conjecture,
% 0.17/0.40      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.17/0.40  
% 0.17/0.40  % (6694)# SZS output end Saturation.
% 0.17/0.40  % (6694)------------------------------
% 0.17/0.40  % (6694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.40  % (6694)Termination reason: Satisfiable
% 0.17/0.40  
% 0.17/0.40  % (6694)Memory used [KB]: 10618
% 0.17/0.40  % (6694)Time elapsed: 0.004 s
% 0.17/0.40  % (6694)------------------------------
% 0.17/0.40  % (6694)------------------------------
% 0.17/0.40  % (6684)Success in time 0.075 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:11 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u23,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u45,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u22,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u25,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u29,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X1)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X1,X0)
    | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)
    | v1_xboole_0(X0) )).

cnf(u24,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u28,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u30,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u35,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u21,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u39,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_enumset1(sK1,sK1,sK1) )).

cnf(u41,negated_conjecture,
    ( sK1 != k2_yellow_0(sK0,k1_enumset1(sK1,sK1,sK1))
    | sK1 != k1_yellow_0(sK0,k1_enumset1(sK1,sK1,sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:54:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (23898)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (23907)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.49  % (23907)# SZS output start Saturation.
% 0.22/0.49  cnf(u23,negated_conjecture,
% 0.22/0.49      v5_orders_2(sK0)).
% 0.22/0.49  
% 0.22/0.49  cnf(u45,negated_conjecture,
% 0.22/0.49      r1_orders_2(sK0,sK1,sK1)).
% 0.22/0.49  
% 0.22/0.49  cnf(u22,negated_conjecture,
% 0.22/0.49      v3_orders_2(sK0)).
% 0.22/0.49  
% 0.22/0.49  cnf(u25,negated_conjecture,
% 0.22/0.49      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.49  
% 0.22/0.49  cnf(u29,axiom,
% 0.22/0.49      ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.49  
% 0.22/0.49  cnf(u34,axiom,
% 0.22/0.49      ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) | v1_xboole_0(X0)).
% 0.22/0.49  
% 0.22/0.49  cnf(u24,negated_conjecture,
% 0.22/0.49      l1_orders_2(sK0)).
% 0.22/0.49  
% 0.22/0.49  cnf(u28,axiom,
% 0.22/0.49      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.22/0.49  
% 0.22/0.49  cnf(u30,axiom,
% 0.22/0.49      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.22/0.49  
% 0.22/0.49  cnf(u35,negated_conjecture,
% 0.22/0.49      l1_struct_0(sK0)).
% 0.22/0.49  
% 0.22/0.49  cnf(u21,negated_conjecture,
% 0.22/0.49      ~v2_struct_0(sK0)).
% 0.22/0.49  
% 0.22/0.49  cnf(u39,negated_conjecture,
% 0.22/0.49      k6_domain_1(u1_struct_0(sK0),sK1) = k1_enumset1(sK1,sK1,sK1)).
% 0.22/0.49  
% 0.22/0.49  cnf(u41,negated_conjecture,
% 0.22/0.49      sK1 != k2_yellow_0(sK0,k1_enumset1(sK1,sK1,sK1)) | sK1 != k1_yellow_0(sK0,k1_enumset1(sK1,sK1,sK1))).
% 0.22/0.49  
% 0.22/0.49  % (23907)# SZS output end Saturation.
% 0.22/0.49  % (23907)------------------------------
% 0.22/0.49  % (23907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (23907)Termination reason: Satisfiable
% 0.22/0.49  
% 0.22/0.49  % (23907)Memory used [KB]: 1663
% 0.22/0.49  % (23907)Time elapsed: 0.053 s
% 0.22/0.49  % (23907)------------------------------
% 0.22/0.49  % (23907)------------------------------
% 0.22/0.49  % (23893)Success in time 0.127 s
%------------------------------------------------------------------------------

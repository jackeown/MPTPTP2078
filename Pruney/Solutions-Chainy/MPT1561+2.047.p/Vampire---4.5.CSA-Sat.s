%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:14 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
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
cnf(u22,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u42,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u21,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u24,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u28,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X1)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u31,axiom,
    ( ~ m1_subset_1(X1,X0)
    | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | v1_xboole_0(X0) )).

cnf(u23,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u27,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u29,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u32,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u20,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u36,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

cnf(u38,negated_conjecture,
    ( sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1))
    | sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:26:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (2101)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.42  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.42  % (2101)# SZS output start Saturation.
% 0.21/0.42  cnf(u22,negated_conjecture,
% 0.21/0.42      v5_orders_2(sK0)).
% 0.21/0.42  
% 0.21/0.42  cnf(u42,negated_conjecture,
% 0.21/0.42      r1_orders_2(sK0,sK1,sK1)).
% 0.21/0.42  
% 0.21/0.42  cnf(u21,negated_conjecture,
% 0.21/0.42      v3_orders_2(sK0)).
% 0.21/0.42  
% 0.21/0.42  cnf(u24,negated_conjecture,
% 0.21/0.42      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.42  
% 0.21/0.42  cnf(u28,axiom,
% 0.21/0.42      ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.21/0.42  
% 0.21/0.42  cnf(u31,axiom,
% 0.21/0.42      ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)).
% 0.21/0.42  
% 0.21/0.42  cnf(u23,negated_conjecture,
% 0.21/0.42      l1_orders_2(sK0)).
% 0.21/0.42  
% 0.21/0.42  cnf(u27,axiom,
% 0.21/0.42      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.21/0.42  
% 0.21/0.42  cnf(u29,axiom,
% 0.21/0.42      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.21/0.42  
% 0.21/0.42  cnf(u32,negated_conjecture,
% 0.21/0.42      l1_struct_0(sK0)).
% 0.21/0.42  
% 0.21/0.42  cnf(u20,negated_conjecture,
% 0.21/0.42      ~v2_struct_0(sK0)).
% 0.21/0.42  
% 0.21/0.42  cnf(u36,negated_conjecture,
% 0.21/0.42      k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)).
% 0.21/0.42  
% 0.21/0.42  cnf(u38,negated_conjecture,
% 0.21/0.42      sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1)) | sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1))).
% 0.21/0.42  
% 0.21/0.42  % (2101)# SZS output end Saturation.
% 0.21/0.42  % (2101)------------------------------
% 0.21/0.42  % (2101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (2101)Termination reason: Satisfiable
% 0.21/0.42  
% 0.21/0.42  % (2101)Memory used [KB]: 1535
% 0.21/0.42  % (2101)Time elapsed: 0.003 s
% 0.21/0.42  % (2101)------------------------------
% 0.21/0.42  % (2101)------------------------------
% 0.21/0.43  % (2085)Success in time 0.066 s
%------------------------------------------------------------------------------

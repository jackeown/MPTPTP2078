%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:07 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    0
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u38,negated_conjecture,
    ( ~ r2_yellow_0(sK0,k2_tarski(sK1,sK1))
    | ~ r1_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

cnf(u22,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u41,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0) )).

% (14521)Refutation not found, incomplete strategy% (14521)------------------------------
% (14521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14521)Termination reason: Refutation not found, incomplete strategy

% (14521)Memory used [KB]: 1535
% (14521)Time elapsed: 0.051 s
% (14521)------------------------------
% (14521)------------------------------
cnf(u21,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u28,axiom,
    ( ~ v3_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_orders_2(X0,X1,X1)
    | v2_struct_0(X0) )).

cnf(u24,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u40,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X0)
    | v2_struct_0(sK0) )).

cnf(u31,axiom,
    ( ~ m1_subset_1(X1,X0)
    | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | v1_xboole_0(X0) )).

cnf(u23,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u39,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X0)
    | v2_struct_0(sK0) )).

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

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:12:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (14519)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (14521)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (14522)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.46  % (14519)# SZS output start Saturation.
% 0.21/0.46  cnf(u38,negated_conjecture,
% 0.21/0.46      ~r2_yellow_0(sK0,k2_tarski(sK1,sK1)) | ~r1_yellow_0(sK0,k2_tarski(sK1,sK1))).
% 0.21/0.46  
% 0.21/0.46  cnf(u22,negated_conjecture,
% 0.21/0.46      v5_orders_2(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u41,negated_conjecture,
% 0.21/0.46      r1_orders_2(sK0,sK1,sK1) | v2_struct_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  % (14521)Refutation not found, incomplete strategy% (14521)------------------------------
% 0.21/0.46  % (14521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (14521)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (14521)Memory used [KB]: 1535
% 0.21/0.46  % (14521)Time elapsed: 0.051 s
% 0.21/0.46  % (14521)------------------------------
% 0.21/0.46  % (14521)------------------------------
% 0.21/0.46  cnf(u21,negated_conjecture,
% 0.21/0.46      v3_orders_2(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u28,axiom,
% 0.21/0.46      ~v3_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X1) | v2_struct_0(X0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u24,negated_conjecture,
% 0.21/0.46      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.46  
% 0.21/0.46  cnf(u40,negated_conjecture,
% 0.21/0.46      ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X0) | v2_struct_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u31,axiom,
% 0.21/0.46      ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u23,negated_conjecture,
% 0.21/0.46      l1_orders_2(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u39,negated_conjecture,
% 0.21/0.46      ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X0) | v2_struct_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u27,axiom,
% 0.21/0.46      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u29,axiom,
% 0.21/0.46      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u32,negated_conjecture,
% 0.21/0.46      l1_struct_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u20,negated_conjecture,
% 0.21/0.46      ~v2_struct_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u36,negated_conjecture,
% 0.21/0.46      k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)).
% 0.21/0.46  
% 0.21/0.46  % (14519)# SZS output end Saturation.
% 0.21/0.46  % (14519)------------------------------
% 0.21/0.46  % (14519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (14519)Termination reason: Satisfiable
% 0.21/0.46  
% 0.21/0.46  % (14519)Memory used [KB]: 1535
% 0.21/0.46  % (14519)Time elapsed: 0.052 s
% 0.21/0.46  % (14519)------------------------------
% 0.21/0.46  % (14519)------------------------------
% 0.21/0.46  % (14522)Refutation not found, incomplete strategy% (14522)------------------------------
% 0.21/0.46  % (14522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (14522)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (14522)Memory used [KB]: 6140
% 0.21/0.46  % (14522)Time elapsed: 0.052 s
% 0.21/0.46  % (14522)------------------------------
% 0.21/0.46  % (14522)------------------------------
% 0.21/0.46  % (14514)Success in time 0.11 s
%------------------------------------------------------------------------------

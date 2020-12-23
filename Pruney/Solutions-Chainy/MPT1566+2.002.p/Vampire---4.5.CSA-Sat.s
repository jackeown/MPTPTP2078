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
% DateTime   : Thu Dec  3 13:16:17 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   42 (  42 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u28,axiom,
    ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u23,negated_conjecture,
    ( ~ r1_orders_2(sK0,k3_yellow_0(sK0),sK1) )).

cnf(u37,negated_conjecture,
    ( r2_lattice3(sK0,X0,sK1)
    | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0)) )).

cnf(u33,negated_conjecture,
    ( r2_lattice3(sK0,k1_xboole_0,sK1) )).

cnf(u40,negated_conjecture,
    ( ~ r2_lattice3(X1,X0,X2)
    | r1_orders_2(X1,sK2(sK0,X0,sK1),X2)
    | ~ m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(X1))
    | r2_lattice3(sK0,X0,sK1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u32,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(sK2(sK0,X0,X1),X0)
    | r2_lattice3(sK0,X0,X1) )).

cnf(u34,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
    | r2_lattice3(sK0,X0,X1) )).

cnf(u21,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u27,axiom,
    ( ~ l1_orders_2(X0)
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_lattice3(X0,X1,X2) )).

cnf(u26,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_lattice3(X0,X1,X2) )).

cnf(u36,negated_conjecture,
    ( r2_hidden(sK2(sK0,X0,sK1),X0)
    | r2_lattice3(sK0,X0,sK1) )).

cnf(u25,axiom,
    ( ~ r2_hidden(X4,X1)
    | r1_orders_2(X0,X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u30,axiom,
    ( ~ r2_hidden(X0,k1_xboole_0) )).

cnf(u24,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u29,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ r2_hidden(X1,X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:34:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (29187)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.43  % (29203)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.22/0.43  % (29187)Refutation not found, incomplete strategy% (29187)------------------------------
% 0.22/0.43  % (29187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (29187)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.43  
% 0.22/0.43  % (29187)Memory used [KB]: 895
% 0.22/0.43  % (29187)Time elapsed: 0.036 s
% 0.22/0.43  % (29187)------------------------------
% 0.22/0.43  % (29187)------------------------------
% 0.22/0.44  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.44  % (29203)# SZS output start Saturation.
% 0.22/0.44  cnf(u28,axiom,
% 0.22/0.44      ~r1_orders_2(X0,sK2(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.22/0.44  
% 0.22/0.44  cnf(u23,negated_conjecture,
% 0.22/0.44      ~r1_orders_2(sK0,k3_yellow_0(sK0),sK1)).
% 0.22/0.44  
% 0.22/0.44  cnf(u37,negated_conjecture,
% 0.22/0.44      r2_lattice3(sK0,X0,sK1) | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0))).
% 0.22/0.44  
% 0.22/0.44  cnf(u33,negated_conjecture,
% 0.22/0.44      r2_lattice3(sK0,k1_xboole_0,sK1)).
% 0.22/0.44  
% 0.22/0.44  cnf(u40,negated_conjecture,
% 0.22/0.44      ~r2_lattice3(X1,X0,X2) | r1_orders_2(X1,sK2(sK0,X0,sK1),X2) | ~m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(X1)) | r2_lattice3(sK0,X0,sK1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1)).
% 0.22/0.44  
% 0.22/0.44  cnf(u22,negated_conjecture,
% 0.22/0.44      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.44  
% 0.22/0.44  cnf(u32,negated_conjecture,
% 0.22/0.44      ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK2(sK0,X0,X1),X0) | r2_lattice3(sK0,X0,X1)).
% 0.22/0.44  
% 0.22/0.44  cnf(u34,negated_conjecture,
% 0.22/0.44      ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)).
% 0.22/0.44  
% 0.22/0.44  cnf(u21,negated_conjecture,
% 0.22/0.44      l1_orders_2(sK0)).
% 0.22/0.44  
% 0.22/0.44  cnf(u27,axiom,
% 0.22/0.44      ~l1_orders_2(X0) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)).
% 0.22/0.44  
% 0.22/0.44  cnf(u26,axiom,
% 0.22/0.44      ~l1_orders_2(X0) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)).
% 0.22/0.44  
% 0.22/0.44  cnf(u36,negated_conjecture,
% 0.22/0.44      r2_hidden(sK2(sK0,X0,sK1),X0) | r2_lattice3(sK0,X0,sK1)).
% 0.22/0.44  
% 0.22/0.44  cnf(u25,axiom,
% 0.22/0.44      ~r2_hidden(X4,X1) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.22/0.44  
% 0.22/0.44  cnf(u30,axiom,
% 0.22/0.44      ~r2_hidden(X0,k1_xboole_0)).
% 0.22/0.44  
% 0.22/0.44  cnf(u24,axiom,
% 0.22/0.44      v1_xboole_0(k1_xboole_0)).
% 0.22/0.44  
% 0.22/0.44  cnf(u29,axiom,
% 0.22/0.44      ~v1_xboole_0(X0) | ~r2_hidden(X1,X0)).
% 0.22/0.44  
% 0.22/0.44  % (29203)# SZS output end Saturation.
% 0.22/0.44  % (29203)------------------------------
% 0.22/0.44  % (29203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (29203)Termination reason: Satisfiable
% 0.22/0.44  
% 0.22/0.44  % (29203)Memory used [KB]: 5373
% 0.22/0.44  % (29203)Time elapsed: 0.050 s
% 0.22/0.44  % (29203)------------------------------
% 0.22/0.44  % (29203)------------------------------
% 0.22/0.44  % (29180)Success in time 0.081 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:00 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    0
%              Number of atoms          :   19 (  19 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u18,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u19,negated_conjecture,
    ( v1_lattice3(sK0) )).

cnf(u25,axiom,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) )).

cnf(u26,axiom,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u23,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK1)
    | sK1 = k13_lattice3(sK0,sK1,sK2) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u21,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u20,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u17,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u28,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u24,negated_conjecture,
    ( sK1 != k13_lattice3(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK2,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n025.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 09:38:50 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.43  % (20405)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.43  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.43  % (20405)# SZS output start Saturation.
% 0.22/0.43  cnf(u18,negated_conjecture,
% 0.22/0.43      v5_orders_2(sK0)).
% 0.22/0.43  
% 0.22/0.43  cnf(u19,negated_conjecture,
% 0.22/0.43      v1_lattice3(sK0)).
% 0.22/0.43  
% 0.22/0.43  cnf(u25,axiom,
% 0.22/0.43      ~v1_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0)).
% 0.22/0.43  
% 0.22/0.43  cnf(u26,axiom,
% 0.22/0.43      r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.43  
% 0.22/0.43  cnf(u23,negated_conjecture,
% 0.22/0.43      r1_orders_2(sK0,sK2,sK1) | sK1 = k13_lattice3(sK0,sK1,sK2)).
% 0.22/0.43  
% 0.22/0.43  cnf(u22,negated_conjecture,
% 0.22/0.43      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.22/0.43  
% 0.22/0.43  cnf(u21,negated_conjecture,
% 0.22/0.43      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.43  
% 0.22/0.43  cnf(u20,negated_conjecture,
% 0.22/0.43      l1_orders_2(sK0)).
% 0.22/0.43  
% 0.22/0.43  cnf(u17,negated_conjecture,
% 0.22/0.43      v3_orders_2(sK0)).
% 0.22/0.43  
% 0.22/0.43  cnf(u28,negated_conjecture,
% 0.22/0.43      ~v2_struct_0(sK0)).
% 0.22/0.43  
% 0.22/0.43  cnf(u24,negated_conjecture,
% 0.22/0.43      sK1 != k13_lattice3(sK0,sK1,sK2) | ~r1_orders_2(sK0,sK2,sK1)).
% 0.22/0.43  
% 0.22/0.43  % (20405)# SZS output end Saturation.
% 0.22/0.43  % (20405)------------------------------
% 0.22/0.43  % (20405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (20405)Termination reason: Satisfiable
% 0.22/0.43  
% 0.22/0.43  % (20405)Memory used [KB]: 6012
% 0.22/0.43  % (20405)Time elapsed: 0.003 s
% 0.22/0.43  % (20405)------------------------------
% 0.22/0.43  % (20405)------------------------------
% 0.22/0.43  % (20395)Success in time 0.074 s
%------------------------------------------------------------------------------

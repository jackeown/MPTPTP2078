%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:14 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    0
%              Number of atoms          :    9 (   9 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u13,negated_conjecture,
    ( ~ r2_yellow_0(sK0,u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k1_xboole_0) )).

cnf(u12,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u11,negated_conjecture,
    ( v1_yellow_0(sK0) )).

cnf(u10,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u9,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u16,axiom,
    ( r1_tarski(k3_xboole_0(X1,X0),X0) )).

cnf(u14,axiom,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) )).

cnf(u15,axiom,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:45:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.42  % (19492)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.13/0.42  % SZS status CounterSatisfiable for theBenchmark
% 0.13/0.42  % (19492)# SZS output start Saturation.
% 0.13/0.42  cnf(u13,negated_conjecture,
% 0.13/0.42      ~r2_yellow_0(sK0,u1_struct_0(sK0)) | ~r1_yellow_0(sK0,k1_xboole_0)).
% 0.13/0.42  
% 0.13/0.42  cnf(u12,negated_conjecture,
% 0.13/0.42      l1_orders_2(sK0)).
% 0.13/0.42  
% 0.13/0.42  cnf(u11,negated_conjecture,
% 0.13/0.42      v1_yellow_0(sK0)).
% 0.13/0.42  
% 0.13/0.42  cnf(u10,negated_conjecture,
% 0.13/0.42      v5_orders_2(sK0)).
% 0.13/0.42  
% 0.13/0.42  cnf(u9,negated_conjecture,
% 0.13/0.42      ~v2_struct_0(sK0)).
% 0.13/0.42  
% 0.13/0.42  cnf(u16,axiom,
% 0.13/0.42      r1_tarski(k3_xboole_0(X1,X0),X0)).
% 0.13/0.42  
% 0.13/0.42  cnf(u14,axiom,
% 0.13/0.42      r1_tarski(k3_xboole_0(X0,X1),X0)).
% 0.13/0.42  
% 0.13/0.42  cnf(u15,axiom,
% 0.13/0.42      k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)).
% 0.13/0.42  
% 0.13/0.42  % (19492)# SZS output end Saturation.
% 0.13/0.42  % (19492)------------------------------
% 0.13/0.42  % (19492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.42  % (19492)Termination reason: Satisfiable
% 0.13/0.42  
% 0.13/0.42  % (19492)Memory used [KB]: 6012
% 0.13/0.42  % (19492)Time elapsed: 0.003 s
% 0.13/0.42  % (19492)------------------------------
% 0.13/0.42  % (19492)------------------------------
% 0.13/0.42  % (19487)Success in time 0.06 s
%------------------------------------------------------------------------------

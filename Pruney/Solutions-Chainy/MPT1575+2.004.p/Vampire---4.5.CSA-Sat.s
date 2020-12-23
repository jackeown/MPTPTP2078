%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:21 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   22 (  22 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    0
%              Number of atoms          :   56 (  56 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal clause size      :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u36,axiom,
    ( sP1(X0)
    | ~ l1_orders_2(X0) )).

cnf(u29,axiom,
    ( ~ sP1(X0)
    | ~ sP0(X0)
    | v3_lattice3(X0) )).

cnf(u28,axiom,
    ( sP0(X0)
    | ~ v3_lattice3(X0)
    | ~ sP1(X0) )).

cnf(u35,axiom,
    ( sP0(X0)
    | ~ r1_orders_2(X0,X2,sK4(X0,X2))
    | ~ r2_lattice3(X0,sK3(X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0)) )).

cnf(u41,axiom,
    ( ~ sP0(X0)
    | v3_lattice3(X0)
    | ~ l1_orders_2(X0) )).

cnf(u26,negated_conjecture,
    ( r1_yellow_0(sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )).

cnf(u24,negated_conjecture,
    ( ~ v2_struct_0(sK2) )).

cnf(u32,axiom,
    ( r1_orders_2(X0,sK5(X0,X4),X6)
    | ~ r2_lattice3(X0,X4,X6)
    | ~ m1_subset_1(X6,u1_struct_0(X0))
    | ~ sP0(X0) )).

cnf(u50,negated_conjecture,
    ( ~ r1_orders_2(sK2,X0,sK4(sK2,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_lattice3(sK2,sK3(sK2),X0) )).

cnf(u34,axiom,
    ( r2_lattice3(X0,sK3(X0),sK4(X0,X2))
    | sP0(X0)
    | ~ r2_lattice3(X0,sK3(X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0)) )).

cnf(u31,axiom,
    ( r2_lattice3(X0,X4,sK5(X0,X4))
    | ~ sP0(X0) )).

cnf(u51,negated_conjecture,
    ( ~ r2_lattice3(sK2,X0,sK4(sK2,sK5(sK2,X0)))
    | ~ r2_lattice3(sK2,sK3(sK2),sK5(sK2,X0))
    | ~ m1_subset_1(sK5(sK2,X0),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4(sK2,sK5(sK2,X0)),u1_struct_0(sK2))
    | ~ sP0(sK2) )).

cnf(u48,axiom,
    ( v3_lattice3(X0)
    | ~ r2_lattice3(X0,sK3(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,sK4(X0,X1))
    | ~ l1_orders_2(X0) )).

cnf(u27,negated_conjecture,
    ( ~ v3_lattice3(sK2) )).

cnf(u25,negated_conjecture,
    ( l1_orders_2(sK2) )).

cnf(u33,axiom,
    ( m1_subset_1(sK4(X0,X2),u1_struct_0(X0))
    | sP0(X0)
    | ~ r2_lattice3(X0,sK3(X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0)) )).

cnf(u30,axiom,
    ( m1_subset_1(sK5(X0,X4),u1_struct_0(X0))
    | ~ sP0(X0) )).

cnf(u40,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) )).

cnf(u39,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u43,axiom,
    ( r1_tarski(k3_xboole_0(X1,X0),X0) )).

cnf(u37,axiom,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) )).

cnf(u38,axiom,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:08:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (14224)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (14222)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.43  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.43  % (14222)# SZS output start Saturation.
% 0.21/0.43  cnf(u36,axiom,
% 0.21/0.43      sP1(X0) | ~l1_orders_2(X0)).
% 0.21/0.43  
% 0.21/0.43  cnf(u29,axiom,
% 0.21/0.43      ~sP1(X0) | ~sP0(X0) | v3_lattice3(X0)).
% 0.21/0.43  
% 0.21/0.43  cnf(u28,axiom,
% 0.21/0.43      sP0(X0) | ~v3_lattice3(X0) | ~sP1(X0)).
% 0.21/0.43  
% 0.21/0.43  cnf(u35,axiom,
% 0.21/0.43      sP0(X0) | ~r1_orders_2(X0,X2,sK4(X0,X2)) | ~r2_lattice3(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))).
% 0.21/0.43  
% 0.21/0.43  cnf(u41,axiom,
% 0.21/0.43      ~sP0(X0) | v3_lattice3(X0) | ~l1_orders_2(X0)).
% 0.21/0.43  
% 0.21/0.43  cnf(u26,negated_conjecture,
% 0.21/0.43      r1_yellow_0(sK2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))).
% 0.21/0.43  
% 0.21/0.43  cnf(u24,negated_conjecture,
% 0.21/0.43      ~v2_struct_0(sK2)).
% 0.21/0.43  
% 0.21/0.43  cnf(u32,axiom,
% 0.21/0.43      r1_orders_2(X0,sK5(X0,X4),X6) | ~r2_lattice3(X0,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~sP0(X0)).
% 0.21/0.43  
% 0.21/0.43  cnf(u50,negated_conjecture,
% 0.21/0.43      ~r1_orders_2(sK2,X0,sK4(sK2,X0)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r2_lattice3(sK2,sK3(sK2),X0)).
% 0.21/0.43  
% 0.21/0.43  cnf(u34,axiom,
% 0.21/0.43      r2_lattice3(X0,sK3(X0),sK4(X0,X2)) | sP0(X0) | ~r2_lattice3(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))).
% 0.21/0.43  
% 0.21/0.43  cnf(u31,axiom,
% 0.21/0.43      r2_lattice3(X0,X4,sK5(X0,X4)) | ~sP0(X0)).
% 0.21/0.43  
% 0.21/0.43  cnf(u51,negated_conjecture,
% 0.21/0.43      ~r2_lattice3(sK2,X0,sK4(sK2,sK5(sK2,X0))) | ~r2_lattice3(sK2,sK3(sK2),sK5(sK2,X0)) | ~m1_subset_1(sK5(sK2,X0),u1_struct_0(sK2)) | ~m1_subset_1(sK4(sK2,sK5(sK2,X0)),u1_struct_0(sK2)) | ~sP0(sK2)).
% 0.21/0.43  
% 0.21/0.43  cnf(u48,axiom,
% 0.21/0.43      v3_lattice3(X0) | ~r2_lattice3(X0,sK3(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,sK4(X0,X1)) | ~l1_orders_2(X0)).
% 0.21/0.43  
% 0.21/0.43  cnf(u27,negated_conjecture,
% 0.21/0.43      ~v3_lattice3(sK2)).
% 0.21/0.43  
% 0.21/0.43  cnf(u25,negated_conjecture,
% 0.21/0.43      l1_orders_2(sK2)).
% 0.21/0.43  
% 0.21/0.43  cnf(u33,axiom,
% 0.21/0.43      m1_subset_1(sK4(X0,X2),u1_struct_0(X0)) | sP0(X0) | ~r2_lattice3(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))).
% 0.21/0.43  
% 0.21/0.43  cnf(u30,axiom,
% 0.21/0.43      m1_subset_1(sK5(X0,X4),u1_struct_0(X0)) | ~sP0(X0)).
% 0.21/0.43  
% 0.21/0.43  cnf(u40,axiom,
% 0.21/0.43      m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)).
% 0.21/0.43  
% 0.21/0.43  cnf(u39,axiom,
% 0.21/0.43      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.21/0.43  
% 0.21/0.43  cnf(u43,axiom,
% 0.21/0.43      r1_tarski(k3_xboole_0(X1,X0),X0)).
% 0.21/0.43  
% 0.21/0.43  cnf(u37,axiom,
% 0.21/0.43      r1_tarski(k3_xboole_0(X0,X1),X0)).
% 0.21/0.43  
% 0.21/0.43  cnf(u38,axiom,
% 0.21/0.43      k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)).
% 0.21/0.43  
% 0.21/0.43  % (14222)# SZS output end Saturation.
% 0.21/0.43  % (14222)------------------------------
% 0.21/0.43  % (14222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (14222)Termination reason: Satisfiable
% 0.21/0.43  
% 0.21/0.43  % (14222)Memory used [KB]: 6140
% 0.21/0.43  % (14222)Time elapsed: 0.004 s
% 0.21/0.43  % (14222)------------------------------
% 0.21/0.43  % (14222)------------------------------
% 0.21/0.43  % (14217)Success in time 0.068 s
%------------------------------------------------------------------------------

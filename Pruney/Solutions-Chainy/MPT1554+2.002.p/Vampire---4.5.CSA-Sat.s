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
% DateTime   : Thu Dec  3 13:16:04 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :   18 (  18 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal clause size      :    4 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u19,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1)
    | sK1 = k1_yellow_0(sK0,sK2) )).

cnf(u12,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | sK1 != k1_yellow_0(sK0,sK2) )).

cnf(u13,negated_conjecture,
    ( r2_lattice3(sK0,sK2,sK1)
    | sK1 = k1_yellow_0(sK0,sK2) )).

cnf(u9,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,X3)
    | sK1 = k1_yellow_0(sK0,sK2) )).

cnf(u10,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK2,sK1)
    | m1_subset_1(sK3,u1_struct_0(sK0))
    | sK1 != k1_yellow_0(sK0,sK2) )).

cnf(u11,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK2,sK1)
    | r2_lattice3(sK0,sK2,sK3)
    | sK1 != k1_yellow_0(sK0,sK2) )).

cnf(u14,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:43:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (27207)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (27217)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.48  % (27202)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (27201)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (27202)Refutation not found, incomplete strategy% (27202)------------------------------
% 0.22/0.49  % (27202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (27202)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (27202)Memory used [KB]: 10490
% 0.22/0.49  % (27202)Time elapsed: 0.068 s
% 0.22/0.49  % (27202)------------------------------
% 0.22/0.49  % (27202)------------------------------
% 0.22/0.49  % (27220)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (27201)Refutation not found, incomplete strategy% (27201)------------------------------
% 0.22/0.49  % (27201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (27201)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (27201)Memory used [KB]: 10490
% 0.22/0.49  % (27201)Time elapsed: 0.079 s
% 0.22/0.49  % (27201)------------------------------
% 0.22/0.49  % (27201)------------------------------
% 0.22/0.49  % (27204)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (27204)Refutation not found, incomplete strategy% (27204)------------------------------
% 0.22/0.49  % (27204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (27204)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (27204)Memory used [KB]: 1535
% 0.22/0.49  % (27204)Time elapsed: 0.074 s
% 0.22/0.49  % (27204)------------------------------
% 0.22/0.49  % (27204)------------------------------
% 0.22/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.49  % (27217)# SZS output start Saturation.
% 0.22/0.49  cnf(u19,negated_conjecture,
% 0.22/0.49      r1_orders_2(sK0,sK1,sK1) | sK1 = k1_yellow_0(sK0,sK2)).
% 0.22/0.49  
% 0.22/0.49  cnf(u12,negated_conjecture,
% 0.22/0.49      ~r1_orders_2(sK0,sK1,sK3) | ~r2_lattice3(sK0,sK2,sK1) | sK1 != k1_yellow_0(sK0,sK2)).
% 0.22/0.49  
% 0.22/0.49  cnf(u13,negated_conjecture,
% 0.22/0.49      r2_lattice3(sK0,sK2,sK1) | sK1 = k1_yellow_0(sK0,sK2)).
% 0.22/0.49  
% 0.22/0.49  cnf(u9,negated_conjecture,
% 0.22/0.49      ~r2_lattice3(sK0,sK2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X3) | sK1 = k1_yellow_0(sK0,sK2)).
% 0.22/0.49  
% 0.22/0.49  cnf(u10,negated_conjecture,
% 0.22/0.49      ~r2_lattice3(sK0,sK2,sK1) | m1_subset_1(sK3,u1_struct_0(sK0)) | sK1 != k1_yellow_0(sK0,sK2)).
% 0.22/0.49  
% 0.22/0.49  cnf(u11,negated_conjecture,
% 0.22/0.49      ~r2_lattice3(sK0,sK2,sK1) | r2_lattice3(sK0,sK2,sK3) | sK1 != k1_yellow_0(sK0,sK2)).
% 0.22/0.49  
% 0.22/0.49  cnf(u14,negated_conjecture,
% 0.22/0.49      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.49  
% 0.22/0.49  % (27217)# SZS output end Saturation.
% 0.22/0.49  % (27217)------------------------------
% 0.22/0.49  % (27217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (27217)Termination reason: Satisfiable
% 0.22/0.49  
% 0.22/0.49  % (27217)Memory used [KB]: 1535
% 0.22/0.49  % (27217)Time elapsed: 0.071 s
% 0.22/0.49  % (27217)------------------------------
% 0.22/0.49  % (27217)------------------------------
% 0.22/0.49  % (27199)Success in time 0.126 s
%------------------------------------------------------------------------------

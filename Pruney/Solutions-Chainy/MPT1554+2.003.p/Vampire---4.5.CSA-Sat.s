%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:04 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (31925)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (31921)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (31921)Refutation not found, incomplete strategy% (31921)------------------------------
% 0.21/0.50  % (31921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31925)Refutation not found, incomplete strategy% (31925)------------------------------
% 0.21/0.51  % (31925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31925)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31925)Memory used [KB]: 10618
% 0.21/0.51  % (31925)Time elapsed: 0.075 s
% 0.21/0.51  % (31925)------------------------------
% 0.21/0.51  % (31925)------------------------------
% 0.21/0.51  % (31933)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (31921)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31921)Memory used [KB]: 10490
% 0.21/0.51  % (31921)Time elapsed: 0.067 s
% 0.21/0.51  % (31921)------------------------------
% 0.21/0.51  % (31921)------------------------------
% 0.21/0.51  % (31932)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (31932)Refutation not found, incomplete strategy% (31932)------------------------------
% 0.21/0.51  % (31932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31932)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31932)Memory used [KB]: 1535
% 0.21/0.51  % (31932)Time elapsed: 0.070 s
% 0.21/0.51  % (31932)------------------------------
% 0.21/0.51  % (31932)------------------------------
% 0.21/0.51  % (31933)Refutation not found, incomplete strategy% (31933)------------------------------
% 0.21/0.51  % (31933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31933)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31933)Memory used [KB]: 10618
% 0.21/0.51  % (31933)Time elapsed: 0.071 s
% 0.21/0.51  % (31933)------------------------------
% 0.21/0.51  % (31933)------------------------------
% 0.21/0.51  % (31926)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (31930)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (31922)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (31930)Refutation not found, incomplete strategy% (31930)------------------------------
% 0.21/0.52  % (31930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31930)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31930)Memory used [KB]: 10618
% 0.21/0.52  % (31930)Time elapsed: 0.089 s
% 0.21/0.52  % (31930)------------------------------
% 0.21/0.52  % (31930)------------------------------
% 0.21/0.52  % (31922)Refutation not found, incomplete strategy% (31922)------------------------------
% 0.21/0.52  % (31922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31922)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31922)Memory used [KB]: 10618
% 0.21/0.52  % (31922)Time elapsed: 0.076 s
% 0.21/0.52  % (31922)------------------------------
% 0.21/0.52  % (31922)------------------------------
% 0.21/0.53  % (31923)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.53  % (31931)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (31923)Refutation not found, incomplete strategy% (31923)------------------------------
% 0.21/0.53  % (31923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31923)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31923)Memory used [KB]: 1535
% 0.21/0.53  % (31923)Time elapsed: 0.099 s
% 0.21/0.53  % (31923)------------------------------
% 0.21/0.53  % (31923)------------------------------
% 0.21/0.53  % (31931)Refutation not found, incomplete strategy% (31931)------------------------------
% 0.21/0.53  % (31931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31931)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31931)Memory used [KB]: 6012
% 0.21/0.53  % (31931)Time elapsed: 0.002 s
% 0.21/0.53  % (31931)------------------------------
% 0.21/0.53  % (31931)------------------------------
% 0.21/0.53  % (31936)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.53  % (31936)# SZS output start Saturation.
% 0.21/0.53  cnf(u19,negated_conjecture,
% 0.21/0.53      r1_orders_2(sK0,sK1,sK1) | sK1 = k1_yellow_0(sK0,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u12,negated_conjecture,
% 0.21/0.53      ~r1_orders_2(sK0,sK1,sK3) | ~r2_lattice3(sK0,sK2,sK1) | sK1 != k1_yellow_0(sK0,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u13,negated_conjecture,
% 0.21/0.53      r2_lattice3(sK0,sK2,sK1) | sK1 = k1_yellow_0(sK0,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u9,negated_conjecture,
% 0.21/0.53      ~r2_lattice3(sK0,sK2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X3) | sK1 = k1_yellow_0(sK0,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u10,negated_conjecture,
% 0.21/0.53      ~r2_lattice3(sK0,sK2,sK1) | m1_subset_1(sK3,u1_struct_0(sK0)) | sK1 != k1_yellow_0(sK0,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u11,negated_conjecture,
% 0.21/0.53      ~r2_lattice3(sK0,sK2,sK1) | r2_lattice3(sK0,sK2,sK3) | sK1 != k1_yellow_0(sK0,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u14,negated_conjecture,
% 0.21/0.53      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.53  
% 0.21/0.53  % (31936)# SZS output end Saturation.
% 0.21/0.53  % (31936)------------------------------
% 0.21/0.53  % (31936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31936)Termination reason: Satisfiable
% 0.21/0.53  
% 0.21/0.53  % (31936)Memory used [KB]: 1535
% 0.21/0.53  % (31936)Time elapsed: 0.101 s
% 0.21/0.53  % (31936)------------------------------
% 0.21/0.53  % (31936)------------------------------
% 0.21/0.53  % (31929)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.54  % (31918)Success in time 0.175 s
%------------------------------------------------------------------------------

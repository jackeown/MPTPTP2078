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
    | sK1 = k2_yellow_0(sK0,sK2) )).

cnf(u12,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | sK1 != k2_yellow_0(sK0,sK2) )).

cnf(u13,negated_conjecture,
    ( r1_lattice3(sK0,sK2,sK1)
    | sK1 = k2_yellow_0(sK0,sK2) )).

cnf(u9,negated_conjecture,
    ( ~ r1_lattice3(sK0,sK2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | r1_orders_2(sK0,X3,sK1)
    | sK1 = k2_yellow_0(sK0,sK2) )).

cnf(u10,negated_conjecture,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | m1_subset_1(sK3,u1_struct_0(sK0))
    | sK1 != k2_yellow_0(sK0,sK2) )).

cnf(u11,negated_conjecture,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | r1_lattice3(sK0,sK2,sK3)
    | sK1 != k2_yellow_0(sK0,sK2) )).

cnf(u14,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:35:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (21787)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (21788)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (21795)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (21787)Refutation not found, incomplete strategy% (21787)------------------------------
% 0.21/0.48  % (21787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21787)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21787)Memory used [KB]: 10490
% 0.21/0.48  % (21787)Time elapsed: 0.064 s
% 0.21/0.48  % (21787)------------------------------
% 0.21/0.48  % (21787)------------------------------
% 0.21/0.48  % (21788)Refutation not found, incomplete strategy% (21788)------------------------------
% 0.21/0.48  % (21788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21788)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21788)Memory used [KB]: 10618
% 0.21/0.48  % (21788)Time elapsed: 0.060 s
% 0.21/0.48  % (21788)------------------------------
% 0.21/0.48  % (21788)------------------------------
% 0.21/0.48  % (21794)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (21791)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (21791)Refutation not found, incomplete strategy% (21791)------------------------------
% 0.21/0.48  % (21791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21791)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21791)Memory used [KB]: 10618
% 0.21/0.48  % (21791)Time elapsed: 0.060 s
% 0.21/0.48  % (21791)------------------------------
% 0.21/0.48  % (21791)------------------------------
% 0.21/0.48  % (21804)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (21804)# SZS output start Saturation.
% 0.21/0.49  cnf(u19,negated_conjecture,
% 0.21/0.49      r1_orders_2(sK0,sK1,sK1) | sK1 = k2_yellow_0(sK0,sK2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u12,negated_conjecture,
% 0.21/0.49      ~r1_orders_2(sK0,sK3,sK1) | ~r1_lattice3(sK0,sK2,sK1) | sK1 != k2_yellow_0(sK0,sK2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u13,negated_conjecture,
% 0.21/0.49      r1_lattice3(sK0,sK2,sK1) | sK1 = k2_yellow_0(sK0,sK2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u9,negated_conjecture,
% 0.21/0.49      ~r1_lattice3(sK0,sK2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_orders_2(sK0,X3,sK1) | sK1 = k2_yellow_0(sK0,sK2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u10,negated_conjecture,
% 0.21/0.49      ~r1_lattice3(sK0,sK2,sK1) | m1_subset_1(sK3,u1_struct_0(sK0)) | sK1 != k2_yellow_0(sK0,sK2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u11,negated_conjecture,
% 0.21/0.49      ~r1_lattice3(sK0,sK2,sK1) | r1_lattice3(sK0,sK2,sK3) | sK1 != k2_yellow_0(sK0,sK2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u14,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  % (21804)# SZS output end Saturation.
% 0.21/0.49  % (21804)------------------------------
% 0.21/0.49  % (21804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (21804)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (21804)Memory used [KB]: 1535
% 0.21/0.49  % (21804)Time elapsed: 0.078 s
% 0.21/0.49  % (21804)------------------------------
% 0.21/0.49  % (21804)------------------------------
% 0.21/0.49  % (21782)Success in time 0.126 s
%------------------------------------------------------------------------------

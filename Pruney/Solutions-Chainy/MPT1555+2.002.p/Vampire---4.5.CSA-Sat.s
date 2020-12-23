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
% (7926)Memory used [KB]: 10618
% (7926)Time elapsed: 0.083 s
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:43:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (7907)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (7917)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.47  % (7907)Refutation not found, incomplete strategy% (7907)------------------------------
% 0.21/0.47  % (7907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (7907)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (7907)Memory used [KB]: 10490
% 0.21/0.47  % (7907)Time elapsed: 0.074 s
% 0.21/0.47  % (7907)------------------------------
% 0.21/0.47  % (7907)------------------------------
% 0.21/0.47  % (7920)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (7925)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.47  % (7920)Refutation not found, incomplete strategy% (7920)------------------------------
% 0.21/0.47  % (7920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (7920)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (7920)Memory used [KB]: 10618
% 0.21/0.47  % (7920)Time elapsed: 0.006 s
% 0.21/0.47  % (7920)------------------------------
% 0.21/0.47  % (7920)------------------------------
% 0.21/0.47  % (7922)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (7917)Refutation not found, incomplete strategy% (7917)------------------------------
% 0.21/0.47  % (7917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (7917)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (7917)Memory used [KB]: 10618
% 0.21/0.47  % (7917)Time elapsed: 0.056 s
% 0.21/0.47  % (7917)------------------------------
% 0.21/0.47  % (7917)------------------------------
% 0.21/0.47  % (7912)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (7919)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (7925)Refutation not found, incomplete strategy% (7925)------------------------------
% 0.21/0.48  % (7925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (7925)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (7925)Memory used [KB]: 6012
% 0.21/0.48  % (7925)Time elapsed: 0.060 s
% 0.21/0.48  % (7925)------------------------------
% 0.21/0.48  % (7925)------------------------------
% 0.21/0.48  % (7912)Refutation not found, incomplete strategy% (7912)------------------------------
% 0.21/0.48  % (7912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (7912)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (7912)Memory used [KB]: 10618
% 0.21/0.48  % (7912)Time elapsed: 0.004 s
% 0.21/0.48  % (7912)------------------------------
% 0.21/0.48  % (7912)------------------------------
% 0.21/0.48  % (7916)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (7916)Refutation not found, incomplete strategy% (7916)------------------------------
% 0.21/0.48  % (7916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (7916)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (7916)Memory used [KB]: 6140
% 0.21/0.48  % (7916)Time elapsed: 0.072 s
% 0.21/0.48  % (7916)------------------------------
% 0.21/0.48  % (7916)------------------------------
% 0.21/0.48  % (7911)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (7909)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (7909)Refutation not found, incomplete strategy% (7909)------------------------------
% 0.21/0.49  % (7909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7909)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7909)Memory used [KB]: 10618
% 0.21/0.49  % (7909)Time elapsed: 0.079 s
% 0.21/0.49  % (7909)------------------------------
% 0.21/0.49  % (7909)------------------------------
% 0.21/0.49  % (7914)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (7919)Refutation not found, incomplete strategy% (7919)------------------------------
% 0.21/0.49  % (7919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7919)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7919)Memory used [KB]: 1535
% 0.21/0.49  % (7919)Time elapsed: 0.087 s
% 0.21/0.49  % (7919)------------------------------
% 0.21/0.49  % (7919)------------------------------
% 0.21/0.49  % (7918)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (7922)Refutation not found, incomplete strategy% (7922)------------------------------
% 0.21/0.49  % (7922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7922)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7922)Memory used [KB]: 10618
% 0.21/0.49  % (7922)Time elapsed: 0.093 s
% 0.21/0.49  % (7922)------------------------------
% 0.21/0.49  % (7922)------------------------------
% 0.21/0.49  % (7918)Refutation not found, incomplete strategy% (7918)------------------------------
% 0.21/0.49  % (7918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7918)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7918)Memory used [KB]: 6012
% 0.21/0.49  % (7918)Time elapsed: 0.002 s
% 0.21/0.49  % (7918)------------------------------
% 0.21/0.49  % (7918)------------------------------
% 0.21/0.49  % (7908)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (7910)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (7926)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (7908)Refutation not found, incomplete strategy% (7908)------------------------------
% 0.21/0.49  % (7908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7908)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7908)Memory used [KB]: 10490
% 0.21/0.49  % (7908)Time elapsed: 0.082 s
% 0.21/0.49  % (7908)------------------------------
% 0.21/0.49  % (7908)------------------------------
% 0.21/0.49  % (7910)Refutation not found, incomplete strategy% (7910)------------------------------
% 0.21/0.49  % (7910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7923)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (7910)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7910)Memory used [KB]: 1535
% 0.21/0.49  % (7910)Time elapsed: 0.086 s
% 0.21/0.49  % (7910)------------------------------
% 0.21/0.49  % (7910)------------------------------
% 0.21/0.49  % (7926)Refutation not found, incomplete strategy% (7926)------------------------------
% 0.21/0.49  % (7926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7926)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (7923)# SZS output start Saturation.
% 0.21/0.49  
% 0.21/0.49  % (7926)Memory used [KB]: 10618
% 0.21/0.49  % (7926)Time elapsed: 0.083 s
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
% 0.21/0.49  % (7923)# SZS output end Saturation.
% 0.21/0.49  % (7923)------------------------------
% 0.21/0.49  % (7923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7923)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (7923)Memory used [KB]: 1535
% 0.21/0.49  % (7923)Time elapsed: 0.083 s
% 0.21/0.49  % (7923)------------------------------
% 0.21/0.49  % (7923)------------------------------
% 0.21/0.49  % (7926)------------------------------
% 0.21/0.49  % (7926)------------------------------
% 0.21/0.49  % (7905)Success in time 0.138 s
%------------------------------------------------------------------------------

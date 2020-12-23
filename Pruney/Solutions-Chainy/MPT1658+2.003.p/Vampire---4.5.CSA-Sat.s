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
% DateTime   : Thu Dec  3 13:17:11 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   35 (  35 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u35,negated_conjecture,
    ( r1_orders_2(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK1)) )).

cnf(u19,axiom,
    ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ r1_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 )).

cnf(u29,negated_conjecture,
    ( r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK1)) )).

cnf(u25,axiom,
    ( ~ r1_lattice3(X0,X1,X3)
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_orders_2(X0,X3,k2_yellow_0(X0,X1)) )).

cnf(u17,axiom,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | k2_yellow_0(X0,X1) = X2 )).

cnf(u18,axiom,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,sK2(X0,X1,X2))
    | k2_yellow_0(X0,X1) = X2 )).

cnf(u14,negated_conjecture,
    ( r2_yellow_0(sK0,sK1) )).

cnf(u26,axiom,
    ( ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) )).

cnf(u27,negated_conjecture,
    ( m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0)) )).

cnf(u13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u16,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u22,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) )).

cnf(u15,negated_conjecture,
    ( k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k4_waybel_0(sK0,sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:06:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.41  % (8757)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.12/0.42  % (8757)Refutation not found, incomplete strategy% (8757)------------------------------
% 0.12/0.42  % (8757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.42  % (8757)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.42  
% 0.12/0.42  % (8757)Memory used [KB]: 6140
% 0.12/0.42  % (8757)Time elapsed: 0.028 s
% 0.12/0.42  % (8757)------------------------------
% 0.12/0.42  % (8757)------------------------------
% 0.20/0.43  % (8765)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.46  % (8768)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.46  % (8775)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.47  % (8764)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (8768)Refutation not found, incomplete strategy% (8768)------------------------------
% 0.20/0.47  % (8768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (8768)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (8768)Memory used [KB]: 10618
% 0.20/0.47  % (8768)Time elapsed: 0.056 s
% 0.20/0.47  % (8768)------------------------------
% 0.20/0.47  % (8768)------------------------------
% 0.20/0.47  % (8775)Refutation not found, incomplete strategy% (8775)------------------------------
% 0.20/0.47  % (8775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (8775)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (8775)Memory used [KB]: 1663
% 0.20/0.47  % (8775)Time elapsed: 0.057 s
% 0.20/0.47  % (8775)------------------------------
% 0.20/0.47  % (8775)------------------------------
% 0.20/0.47  % (8777)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (8760)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (8758)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (8772)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (8777)Refutation not found, incomplete strategy% (8777)------------------------------
% 0.20/0.47  % (8777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (8777)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (8777)Memory used [KB]: 10490
% 0.20/0.47  % (8777)Time elapsed: 0.057 s
% 0.20/0.47  % (8777)------------------------------
% 0.20/0.47  % (8777)------------------------------
% 0.20/0.48  % (8758)Refutation not found, incomplete strategy% (8758)------------------------------
% 0.20/0.48  % (8758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (8758)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (8758)Memory used [KB]: 10490
% 0.20/0.48  % (8758)Time elapsed: 0.068 s
% 0.20/0.48  % (8758)------------------------------
% 0.20/0.48  % (8758)------------------------------
% 0.20/0.48  % (8760)Refutation not found, incomplete strategy% (8760)------------------------------
% 0.20/0.48  % (8760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (8760)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (8760)Memory used [KB]: 10618
% 0.20/0.48  % (8760)Time elapsed: 0.068 s
% 0.20/0.48  % (8760)------------------------------
% 0.20/0.48  % (8760)------------------------------
% 0.20/0.48  % (8763)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (8763)Refutation not found, incomplete strategy% (8763)------------------------------
% 0.20/0.48  % (8763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (8763)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (8763)Memory used [KB]: 10618
% 0.20/0.48  % (8763)Time elapsed: 0.046 s
% 0.20/0.48  % (8763)------------------------------
% 0.20/0.48  % (8763)------------------------------
% 0.20/0.48  % (8771)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (8766)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (8771)Refutation not found, incomplete strategy% (8771)------------------------------
% 0.20/0.49  % (8771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (8771)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (8771)Memory used [KB]: 10618
% 0.20/0.49  % (8771)Time elapsed: 0.044 s
% 0.20/0.49  % (8771)------------------------------
% 0.20/0.49  % (8771)------------------------------
% 0.20/0.49  % (8766)Refutation not found, incomplete strategy% (8766)------------------------------
% 0.20/0.49  % (8766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (8766)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (8766)Memory used [KB]: 10618
% 0.20/0.49  % (8766)Time elapsed: 0.080 s
% 0.20/0.49  % (8766)------------------------------
% 0.20/0.49  % (8766)------------------------------
% 0.20/0.49  % (8759)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (8774)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (8759)Refutation not found, incomplete strategy% (8759)------------------------------
% 0.20/0.49  % (8759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (8762)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (8770)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (8769)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (8770)Refutation not found, incomplete strategy% (8770)------------------------------
% 0.20/0.49  % (8770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (8770)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (8770)Memory used [KB]: 1535
% 0.20/0.49  % (8770)Time elapsed: 0.077 s
% 0.20/0.49  % (8770)------------------------------
% 0.20/0.49  % (8770)------------------------------
% 0.20/0.49  % (8773)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (8769)Refutation not found, incomplete strategy% (8769)------------------------------
% 0.20/0.49  % (8769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (8769)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (8769)Memory used [KB]: 6140
% 0.20/0.49  % (8769)Time elapsed: 0.052 s
% 0.20/0.49  % (8769)------------------------------
% 0.20/0.49  % (8769)------------------------------
% 0.20/0.49  % (8776)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.49  % (8767)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (8767)Refutation not found, incomplete strategy% (8767)------------------------------
% 0.20/0.50  % (8767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (8767)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (8767)Memory used [KB]: 6012
% 0.20/0.50  % (8767)Time elapsed: 0.092 s
% 0.20/0.50  % (8767)------------------------------
% 0.20/0.50  % (8767)------------------------------
% 0.20/0.50  % (8759)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (8759)Memory used [KB]: 10618
% 0.20/0.50  % (8759)Time elapsed: 0.076 s
% 0.20/0.50  % (8759)------------------------------
% 0.20/0.50  % (8759)------------------------------
% 0.20/0.50  % (8761)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.50  % (8774)# SZS output start Saturation.
% 0.20/0.50  cnf(u35,negated_conjecture,
% 0.20/0.50      r1_orders_2(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK1))).
% 0.20/0.50  
% 0.20/0.50  cnf(u19,axiom,
% 0.20/0.50      ~r1_orders_2(X0,sK2(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~r1_lattice3(X0,X1,X2) | ~l1_orders_2(X0) | k2_yellow_0(X0,X1) = X2).
% 0.20/0.50  
% 0.20/0.50  cnf(u29,negated_conjecture,
% 0.20/0.50      r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK1))).
% 0.20/0.50  
% 0.20/0.50  cnf(u25,axiom,
% 0.20/0.50      ~r1_lattice3(X0,X1,X3) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X3,k2_yellow_0(X0,X1))).
% 0.20/0.50  
% 0.20/0.50  cnf(u17,axiom,
% 0.20/0.50      ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | k2_yellow_0(X0,X1) = X2).
% 0.20/0.50  
% 0.20/0.50  cnf(u18,axiom,
% 0.20/0.50      ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,sK2(X0,X1,X2)) | k2_yellow_0(X0,X1) = X2).
% 0.20/0.50  
% 0.20/0.50  cnf(u14,negated_conjecture,
% 0.20/0.50      r2_yellow_0(sK0,sK1)).
% 0.20/0.50  
% 0.20/0.50  cnf(u26,axiom,
% 0.20/0.50      ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))).
% 0.20/0.50  
% 0.20/0.50  cnf(u27,negated_conjecture,
% 0.20/0.50      m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0))).
% 0.20/0.50  
% 0.20/0.50  cnf(u13,negated_conjecture,
% 0.20/0.50      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.50  
% 0.20/0.50  cnf(u16,negated_conjecture,
% 0.20/0.50      l1_orders_2(sK0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u22,axiom,
% 0.20/0.50      ~l1_orders_2(X0) | m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))).
% 0.20/0.50  
% 0.20/0.50  cnf(u15,negated_conjecture,
% 0.20/0.50      k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k4_waybel_0(sK0,sK1))).
% 0.20/0.50  
% 0.20/0.50  % (8774)# SZS output end Saturation.
% 0.20/0.50  % (8774)------------------------------
% 0.20/0.50  % (8774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (8774)Termination reason: Satisfiable
% 0.20/0.50  
% 0.20/0.50  % (8774)Memory used [KB]: 1663
% 0.20/0.50  % (8774)Time elapsed: 0.091 s
% 0.20/0.50  % (8774)------------------------------
% 0.20/0.50  % (8774)------------------------------
% 0.20/0.50  % (8754)Success in time 0.146 s
%------------------------------------------------------------------------------

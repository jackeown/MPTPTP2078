%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:07 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
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
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK1)) )).

cnf(u19,axiom,
    ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 )).

cnf(u29,negated_conjecture,
    ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK1)) )).

cnf(u25,axiom,
    ( ~ r2_lattice3(X0,X1,X3)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X3) )).

cnf(u17,axiom,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2 )).

cnf(u18,axiom,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,sK2(X0,X1,X2))
    | k1_yellow_0(X0,X1) = X2 )).

cnf(u14,negated_conjecture,
    ( r1_yellow_0(sK0,sK1) )).

cnf(u26,axiom,
    ( ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) )).

cnf(u27,negated_conjecture,
    ( m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) )).

cnf(u13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u16,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u22,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) )).

cnf(u15,negated_conjecture,
    ( k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,k3_waybel_0(sK0,sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:57:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (13664)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (13672)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (13659)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (13669)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (13662)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (13669)Refutation not found, incomplete strategy% (13669)------------------------------
% 0.22/0.50  % (13669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (13669)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (13669)Memory used [KB]: 1535
% 0.22/0.50  % (13669)Time elapsed: 0.095 s
% 0.22/0.50  % (13669)------------------------------
% 0.22/0.50  % (13669)------------------------------
% 0.22/0.50  % (13657)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (13657)Refutation not found, incomplete strategy% (13657)------------------------------
% 0.22/0.50  % (13657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (13657)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (13657)Memory used [KB]: 10490
% 0.22/0.50  % (13657)Time elapsed: 0.078 s
% 0.22/0.50  % (13657)------------------------------
% 0.22/0.50  % (13657)------------------------------
% 0.22/0.51  % (13661)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (13656)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (13656)Refutation not found, incomplete strategy% (13656)------------------------------
% 0.22/0.51  % (13656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13656)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13656)Memory used [KB]: 6140
% 0.22/0.51  % (13656)Time elapsed: 0.091 s
% 0.22/0.51  % (13656)------------------------------
% 0.22/0.51  % (13656)------------------------------
% 0.22/0.51  % (13671)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (13674)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (13665)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (13670)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (13674)Refutation not found, incomplete strategy% (13674)------------------------------
% 0.22/0.51  % (13674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13674)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13674)Memory used [KB]: 1663
% 0.22/0.51  % (13674)Time elapsed: 0.110 s
% 0.22/0.51  % (13674)------------------------------
% 0.22/0.51  % (13674)------------------------------
% 0.22/0.51  % (13660)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (13676)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (13665)Refutation not found, incomplete strategy% (13665)------------------------------
% 0.22/0.51  % (13665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13665)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13665)Memory used [KB]: 10618
% 0.22/0.51  % (13665)Time elapsed: 0.100 s
% 0.22/0.51  % (13665)------------------------------
% 0.22/0.51  % (13665)------------------------------
% 0.22/0.51  % (13676)Refutation not found, incomplete strategy% (13676)------------------------------
% 0.22/0.51  % (13676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13676)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13676)Memory used [KB]: 10490
% 0.22/0.51  % (13676)Time elapsed: 0.103 s
% 0.22/0.51  % (13676)------------------------------
% 0.22/0.51  % (13676)------------------------------
% 0.22/0.51  % (13659)Refutation not found, incomplete strategy% (13659)------------------------------
% 0.22/0.51  % (13659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13659)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13659)Memory used [KB]: 10618
% 0.22/0.51  % (13659)Time elapsed: 0.102 s
% 0.22/0.51  % (13659)------------------------------
% 0.22/0.51  % (13659)------------------------------
% 0.22/0.51  % (13673)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (13673)# SZS output start Saturation.
% 0.22/0.51  cnf(u35,negated_conjecture,
% 0.22/0.51      r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u19,axiom,
% 0.22/0.51      ~r1_orders_2(X0,X2,sK2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0) | k1_yellow_0(X0,X1) = X2).
% 0.22/0.51  
% 0.22/0.51  cnf(u29,negated_conjecture,
% 0.22/0.51      r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u25,axiom,
% 0.22/0.51      ~r2_lattice3(X0,X1,X3) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,k1_yellow_0(X0,X1),X3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u17,axiom,
% 0.22/0.51      ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X1) = X2).
% 0.22/0.51  
% 0.22/0.51  cnf(u18,axiom,
% 0.22/0.51      ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,sK2(X0,X1,X2)) | k1_yellow_0(X0,X1) = X2).
% 0.22/0.51  
% 0.22/0.51  cnf(u14,negated_conjecture,
% 0.22/0.51      r1_yellow_0(sK0,sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u26,axiom,
% 0.22/0.51      ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u27,negated_conjecture,
% 0.22/0.51      m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u13,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.51  
% 0.22/0.51  cnf(u16,negated_conjecture,
% 0.22/0.51      l1_orders_2(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u22,axiom,
% 0.22/0.51      ~l1_orders_2(X0) | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u15,negated_conjecture,
% 0.22/0.51      k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,k3_waybel_0(sK0,sK1))).
% 0.22/0.51  
% 0.22/0.51  % (13673)# SZS output end Saturation.
% 0.22/0.51  % (13673)------------------------------
% 0.22/0.51  % (13673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13673)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (13673)Memory used [KB]: 1663
% 0.22/0.51  % (13673)Time elapsed: 0.104 s
% 0.22/0.51  % (13673)------------------------------
% 0.22/0.51  % (13673)------------------------------
% 0.22/0.52  % (13655)Success in time 0.152 s
%------------------------------------------------------------------------------

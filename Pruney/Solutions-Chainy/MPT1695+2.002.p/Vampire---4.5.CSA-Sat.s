%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:25 EST 2020

% Result     : CounterSatisfiable 1.26s
% Output     : Saturation 1.26s
% Verified   : 
% Statistics : Number of clauses        :   24 (  24 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    0
%              Number of atoms          :   96 (  96 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal clause size      :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u17,negated_conjecture,
    ( ~ v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0) )).

cnf(u18,negated_conjecture,
    ( ~ v24_waybel_0(sK0)
    | v1_waybel_0(sK1,sK0) )).

cnf(u19,negated_conjecture,
    ( ~ v24_waybel_0(sK0)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u24,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u46,axiom,
    ( ~ r2_lattice3(X0,X1,X3)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X3) )).

cnf(u36,axiom,
    ( ~ r2_lattice3(X0,X2,X1)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | r2_lattice3(X0,X2,sK3(X0,X1,X2))
    | k1_yellow_0(X0,X2) = X1 )).

cnf(u35,axiom,
    ( ~ r2_lattice3(X0,X2,X1)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | k1_yellow_0(X0,X2) = X1 )).

cnf(u33,axiom,
    ( ~ r2_lattice3(X0,X2,X1)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | r2_lattice3(X0,X2,sK3(X0,X1,X2))
    | r1_yellow_0(X0,X2) )).

cnf(u32,axiom,
    ( ~ r2_lattice3(X0,X2,X1)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | r1_yellow_0(X0,X2) )).

cnf(u27,axiom,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,sK2(X0,X1,X2))
    | k1_yellow_0(X0,X1) = X2 )).

cnf(u26,axiom,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2 )).

cnf(u47,axiom,
    ( ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) )).

cnf(u20,negated_conjecture,
    ( ~ r1_yellow_0(sK0,sK1)
    | ~ v24_waybel_0(sK0) )).

cnf(u28,axiom,
    ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 )).

cnf(u40,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | r3_orders_2(X0,X1,X2) )).

cnf(u34,axiom,
    ( ~ r1_orders_2(X0,X1,sK3(X0,X1,X2))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_lattice3(X0,X2,X1)
    | ~ v5_orders_2(X0)
    | r1_yellow_0(X0,X2) )).

cnf(u37,axiom,
    ( ~ r1_orders_2(X0,X1,sK3(X0,X1,X2))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_lattice3(X0,X2,X1)
    | ~ v5_orders_2(X0)
    | k1_yellow_0(X0,X2) = X1 )).

cnf(u41,axiom,
    ( ~ r3_orders_2(X0,X1,X2)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X2)
    | v2_struct_0(X0) )).

cnf(u48,negated_conjecture,
    ( m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) )).

cnf(u21,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_0(X1,sK0)
    | v1_xboole_0(X1)
    | r1_yellow_0(sK0,X1)
    | v24_waybel_0(sK0) )).

cnf(u25,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u39,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) )).

cnf(u23,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u22,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:23:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (26700)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (26700)Refutation not found, incomplete strategy% (26700)------------------------------
% 0.22/0.47  % (26700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (26700)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (26700)Memory used [KB]: 6140
% 0.22/0.47  % (26700)Time elapsed: 0.052 s
% 0.22/0.47  % (26700)------------------------------
% 0.22/0.47  % (26700)------------------------------
% 0.22/0.48  % (26708)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (26702)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (26710)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (26699)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (26698)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (26704)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (26697)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.26/0.52  % (26704)Refutation not found, incomplete strategy% (26704)------------------------------
% 1.26/0.52  % (26704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (26704)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.52  
% 1.26/0.52  % (26704)Memory used [KB]: 10618
% 1.26/0.52  % (26704)Time elapsed: 0.090 s
% 1.26/0.52  % (26704)------------------------------
% 1.26/0.52  % (26704)------------------------------
% 1.26/0.52  % (26697)Refutation not found, incomplete strategy% (26697)------------------------------
% 1.26/0.52  % (26697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (26697)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.52  
% 1.26/0.52  % (26697)Memory used [KB]: 10618
% 1.26/0.52  % (26697)Time elapsed: 0.090 s
% 1.26/0.52  % (26697)------------------------------
% 1.26/0.52  % (26697)------------------------------
% 1.26/0.52  % (26703)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.26/0.52  % (26696)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.52  % (26696)Refutation not found, incomplete strategy% (26696)------------------------------
% 1.26/0.52  % (26696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (26706)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.26/0.52  % (26705)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.26/0.52  % (26715)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.26/0.52  % (26713)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.26/0.52  % (26701)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 1.26/0.52  % (26706)Refutation not found, incomplete strategy% (26706)------------------------------
% 1.26/0.52  % (26706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (26706)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.52  
% 1.26/0.52  % (26706)Memory used [KB]: 10618
% 1.26/0.52  % (26706)Time elapsed: 0.104 s
% 1.26/0.52  % (26706)------------------------------
% 1.26/0.52  % (26706)------------------------------
% 1.26/0.52  % (26715)Refutation not found, incomplete strategy% (26715)------------------------------
% 1.26/0.52  % (26715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (26715)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.52  
% 1.26/0.52  % (26715)Memory used [KB]: 10618
% 1.26/0.52  % (26715)Time elapsed: 0.104 s
% 1.26/0.52  % (26715)------------------------------
% 1.26/0.52  % (26715)------------------------------
% 1.26/0.52  % (26713)Refutation not found, incomplete strategy% (26713)------------------------------
% 1.26/0.52  % (26713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (26707)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.53  % (26698)Refutation not found, incomplete strategy% (26698)------------------------------
% 1.26/0.53  % (26698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (26698)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (26698)Memory used [KB]: 10618
% 1.26/0.53  % (26698)Time elapsed: 0.100 s
% 1.26/0.53  % (26698)------------------------------
% 1.26/0.53  % (26698)------------------------------
% 1.26/0.53  % (26712)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.26/0.53  % (26696)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (26696)Memory used [KB]: 10618
% 1.26/0.53  % (26696)Time elapsed: 0.101 s
% 1.26/0.53  % (26696)------------------------------
% 1.26/0.53  % (26696)------------------------------
% 1.26/0.53  % (26707)Refutation not found, incomplete strategy% (26707)------------------------------
% 1.26/0.53  % (26707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (26707)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (26707)Memory used [KB]: 6012
% 1.26/0.53  % (26707)Time elapsed: 0.002 s
% 1.26/0.53  % (26707)------------------------------
% 1.26/0.53  % (26707)------------------------------
% 1.26/0.53  % (26714)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.26/0.53  % SZS status CounterSatisfiable for theBenchmark
% 1.26/0.53  % (26712)# SZS output start Saturation.
% 1.26/0.53  cnf(u17,negated_conjecture,
% 1.26/0.53      ~v1_xboole_0(sK1) | ~v24_waybel_0(sK0)).
% 1.26/0.53  
% 1.26/0.53  cnf(u18,negated_conjecture,
% 1.26/0.53      ~v24_waybel_0(sK0) | v1_waybel_0(sK1,sK0)).
% 1.26/0.53  
% 1.26/0.53  cnf(u19,negated_conjecture,
% 1.26/0.53      ~v24_waybel_0(sK0) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.26/0.53  
% 1.26/0.53  cnf(u24,negated_conjecture,
% 1.26/0.53      v5_orders_2(sK0)).
% 1.26/0.53  
% 1.26/0.53  cnf(u46,axiom,
% 1.26/0.53      ~r2_lattice3(X0,X1,X3) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,k1_yellow_0(X0,X1),X3)).
% 1.26/0.53  
% 1.26/0.53  cnf(u36,axiom,
% 1.26/0.53      ~r2_lattice3(X0,X2,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_orders_2(X0) | r2_lattice3(X0,X2,sK3(X0,X1,X2)) | k1_yellow_0(X0,X2) = X1).
% 1.26/0.53  
% 1.26/0.53  cnf(u35,axiom,
% 1.26/0.53      ~r2_lattice3(X0,X2,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_orders_2(X0) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X2) = X1).
% 1.26/0.53  
% 1.26/0.53  cnf(u33,axiom,
% 1.26/0.53      ~r2_lattice3(X0,X2,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_orders_2(X0) | r2_lattice3(X0,X2,sK3(X0,X1,X2)) | r1_yellow_0(X0,X2)).
% 1.26/0.53  
% 1.26/0.53  cnf(u32,axiom,
% 1.26/0.53      ~r2_lattice3(X0,X2,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_orders_2(X0) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r1_yellow_0(X0,X2)).
% 1.26/0.53  
% 1.26/0.53  cnf(u27,axiom,
% 1.26/0.53      ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,sK2(X0,X1,X2)) | k1_yellow_0(X0,X1) = X2).
% 1.26/0.53  
% 1.26/0.53  cnf(u26,axiom,
% 1.26/0.53      ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X1) = X2).
% 1.26/0.53  
% 1.26/0.53  cnf(u47,axiom,
% 1.26/0.53      ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))).
% 1.26/0.53  
% 1.26/0.53  cnf(u20,negated_conjecture,
% 1.26/0.53      ~r1_yellow_0(sK0,sK1) | ~v24_waybel_0(sK0)).
% 1.26/0.53  
% 1.26/0.53  cnf(u28,axiom,
% 1.26/0.53      ~r1_orders_2(X0,X2,sK2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0) | k1_yellow_0(X0,X1) = X2).
% 1.26/0.53  
% 1.26/0.53  cnf(u40,axiom,
% 1.26/0.53      ~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r3_orders_2(X0,X1,X2)).
% 1.26/0.53  
% 1.26/0.53  cnf(u34,axiom,
% 1.26/0.53      ~r1_orders_2(X0,X1,sK3(X0,X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~v5_orders_2(X0) | r1_yellow_0(X0,X2)).
% 1.26/0.53  
% 1.26/0.53  cnf(u37,axiom,
% 1.26/0.53      ~r1_orders_2(X0,X1,sK3(X0,X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~v5_orders_2(X0) | k1_yellow_0(X0,X2) = X1).
% 1.26/0.53  
% 1.26/0.53  cnf(u41,axiom,
% 1.26/0.53      ~r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | v2_struct_0(X0)).
% 1.26/0.53  
% 1.26/0.53  cnf(u48,negated_conjecture,
% 1.26/0.53      m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))).
% 1.26/0.53  
% 1.26/0.53  cnf(u21,negated_conjecture,
% 1.26/0.53      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_waybel_0(X1,sK0) | v1_xboole_0(X1) | r1_yellow_0(sK0,X1) | v24_waybel_0(sK0)).
% 1.26/0.53  
% 1.26/0.53  cnf(u25,negated_conjecture,
% 1.26/0.53      l1_orders_2(sK0)).
% 1.26/0.53  
% 1.26/0.53  cnf(u39,axiom,
% 1.26/0.53      ~l1_orders_2(X0) | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))).
% 1.26/0.53  
% 1.26/0.53  cnf(u23,negated_conjecture,
% 1.26/0.53      v3_orders_2(sK0)).
% 1.26/0.53  
% 1.26/0.53  cnf(u22,negated_conjecture,
% 1.26/0.53      ~v2_struct_0(sK0)).
% 1.26/0.53  
% 1.26/0.53  % (26712)# SZS output end Saturation.
% 1.26/0.53  % (26712)------------------------------
% 1.26/0.53  % (26712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (26712)Termination reason: Satisfiable
% 1.26/0.53  
% 1.26/0.53  % (26712)Memory used [KB]: 1663
% 1.26/0.53  % (26712)Time elapsed: 0.106 s
% 1.26/0.53  % (26712)------------------------------
% 1.26/0.53  % (26712)------------------------------
% 1.26/0.53  % (26694)Success in time 0.166 s
%------------------------------------------------------------------------------

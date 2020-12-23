%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:14 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   21 (  21 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    0
%              Number of atoms          :  100 ( 100 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal clause size      :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u25,negated_conjecture,
    ( ~ r2_hidden(k12_lattice3(sK0,sK2,sK3),sK1)
    | ~ v2_waybel_0(sK1,sK0) )).

cnf(u23,negated_conjecture,
    ( ~ v2_waybel_0(sK1,sK0)
    | r2_hidden(sK2,sK1) )).

cnf(u24,negated_conjecture,
    ( ~ v2_waybel_0(sK1,sK0)
    | r2_hidden(sK3,sK1) )).

cnf(u22,negated_conjecture,
    ( ~ v2_waybel_0(sK1,sK0)
    | m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u26,negated_conjecture,
    ( ~ v2_waybel_0(sK1,sK0)
    | m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u48,axiom,
    ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ v5_orders_2(X0)
    | k11_lattice3(X0,X1,X2) = X3 )).

cnf(u52,axiom,
    ( ~ r1_orders_2(X0,X4,X1)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X4,X2)
    | r1_orders_2(X0,X4,k11_lattice3(X0,X1,X2)) )).

cnf(u49,axiom,
    ( ~ r1_orders_2(X0,X3,X1)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
    | k11_lattice3(X0,X1,X2) = X3 )).

cnf(u50,axiom,
    ( ~ r1_orders_2(X0,X3,X1)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
    | k11_lattice3(X0,X1,X2) = X3 )).

cnf(u51,axiom,
    ( ~ r1_orders_2(X0,X3,X1)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X2)
    | m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0))
    | k11_lattice3(X0,X1,X2) = X3 )).

cnf(u27,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u21,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | ~ r2_hidden(X2,sK1)
    | ~ r2_hidden(X3,sK1)
    | r2_hidden(k12_lattice3(sK0,X2,X3),sK1)
    | v2_waybel_0(sK1,sK0) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) )).

cnf(u53,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) )).

cnf(u54,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) )).

cnf(u39,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) )).

cnf(u28,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u31,axiom,
    ( ~ v2_struct_0(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0) )).

cnf(u29,negated_conjecture,
    ( v2_lattice3(sK0) )).

cnf(u30,negated_conjecture,
    ( l1_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:50:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (18351)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.44  % (18359)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.44  % (18352)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.44  % (18345)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.45  % (18348)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.45  % (18350)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.46  % (18361)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.46  % (18363)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (18353)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (18344)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (18356)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (18356)Refutation not found, incomplete strategy% (18356)------------------------------
% 0.20/0.47  % (18356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (18356)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (18356)Memory used [KB]: 1663
% 0.20/0.47  % (18356)Time elapsed: 0.070 s
% 0.20/0.47  % (18356)------------------------------
% 0.20/0.47  % (18356)------------------------------
% 0.20/0.47  % (18346)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (18349)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (18347)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % (18343)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (18343)Refutation not found, incomplete strategy% (18343)------------------------------
% 0.20/0.48  % (18343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (18343)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (18343)Memory used [KB]: 6140
% 0.20/0.48  % (18343)Time elapsed: 0.062 s
% 0.20/0.48  % (18343)------------------------------
% 0.20/0.48  % (18343)------------------------------
% 0.20/0.48  % (18358)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (18354)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (18357)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (18363)Refutation not found, incomplete strategy% (18363)------------------------------
% 0.20/0.48  % (18363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (18363)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (18363)Memory used [KB]: 10618
% 0.20/0.48  % (18363)Time elapsed: 0.076 s
% 0.20/0.48  % (18363)------------------------------
% 0.20/0.48  % (18363)------------------------------
% 0.20/0.48  % (18344)Refutation not found, incomplete strategy% (18344)------------------------------
% 0.20/0.48  % (18344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (18354)Refutation not found, incomplete strategy% (18354)------------------------------
% 0.20/0.48  % (18354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (18354)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (18354)Memory used [KB]: 10618
% 0.20/0.48  % (18354)Time elapsed: 0.077 s
% 0.20/0.48  % (18354)------------------------------
% 0.20/0.48  % (18354)------------------------------
% 0.20/0.48  % (18344)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (18344)Memory used [KB]: 10618
% 0.20/0.48  % (18344)Time elapsed: 0.078 s
% 0.20/0.48  % (18344)------------------------------
% 0.20/0.48  % (18344)------------------------------
% 0.20/0.48  % (18357)Refutation not found, incomplete strategy% (18357)------------------------------
% 0.20/0.48  % (18357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (18357)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (18357)Memory used [KB]: 10618
% 0.20/0.48  % (18357)Time elapsed: 0.072 s
% 0.20/0.48  % (18357)------------------------------
% 0.20/0.48  % (18357)------------------------------
% 0.20/0.49  % (18355)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (18355)Refutation not found, incomplete strategy% (18355)------------------------------
% 0.20/0.49  % (18355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (18355)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (18355)Memory used [KB]: 6012
% 0.20/0.49  % (18355)Time elapsed: 0.002 s
% 0.20/0.49  % (18355)------------------------------
% 0.20/0.49  % (18355)------------------------------
% 0.20/0.49  % (18360)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.49  % (18360)# SZS output start Saturation.
% 0.20/0.49  cnf(u25,negated_conjecture,
% 0.20/0.49      ~r2_hidden(k12_lattice3(sK0,sK2,sK3),sK1) | ~v2_waybel_0(sK1,sK0)).
% 0.20/0.49  
% 0.20/0.49  cnf(u23,negated_conjecture,
% 0.20/0.49      ~v2_waybel_0(sK1,sK0) | r2_hidden(sK2,sK1)).
% 0.20/0.49  
% 0.20/0.49  cnf(u24,negated_conjecture,
% 0.20/0.49      ~v2_waybel_0(sK1,sK0) | r2_hidden(sK3,sK1)).
% 0.20/0.49  
% 0.20/0.49  cnf(u22,negated_conjecture,
% 0.20/0.49      ~v2_waybel_0(sK1,sK0) | m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.20/0.49  
% 0.20/0.49  cnf(u26,negated_conjecture,
% 0.20/0.49      ~v2_waybel_0(sK1,sK0) | m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.49  
% 0.20/0.49  cnf(u48,axiom,
% 0.20/0.49      ~r1_orders_2(X0,sK4(X0,X1,X2,X3),X3) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | ~v5_orders_2(X0) | k11_lattice3(X0,X1,X2) = X3).
% 0.20/0.49  
% 0.20/0.49  cnf(u52,axiom,
% 0.20/0.49      ~r1_orders_2(X0,X4,X1) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X4,X2) | r1_orders_2(X0,X4,k11_lattice3(X0,X1,X2))).
% 0.20/0.49  
% 0.20/0.49  cnf(u49,axiom,
% 0.20/0.49      ~r1_orders_2(X0,X3,X1) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK4(X0,X1,X2,X3),X2) | k11_lattice3(X0,X1,X2) = X3).
% 0.20/0.49  
% 0.20/0.49  cnf(u50,axiom,
% 0.20/0.49      ~r1_orders_2(X0,X3,X1) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK4(X0,X1,X2,X3),X1) | k11_lattice3(X0,X1,X2) = X3).
% 0.20/0.49  
% 0.20/0.49  cnf(u51,axiom,
% 0.20/0.49      ~r1_orders_2(X0,X3,X1) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = X3).
% 0.20/0.49  
% 0.20/0.49  cnf(u27,negated_conjecture,
% 0.20/0.49      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.49  
% 0.20/0.49  cnf(u21,negated_conjecture,
% 0.20/0.49      ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | ~r2_hidden(X3,sK1) | r2_hidden(k12_lattice3(sK0,X2,X3),sK1) | v2_waybel_0(sK1,sK0)).
% 0.20/0.49  
% 0.20/0.49  cnf(u41,axiom,
% 0.20/0.49      ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))).
% 0.20/0.49  
% 0.20/0.49  cnf(u53,axiom,
% 0.20/0.49      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)).
% 0.20/0.49  
% 0.20/0.49  cnf(u54,axiom,
% 0.20/0.49      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)).
% 0.20/0.49  
% 0.20/0.49  cnf(u39,axiom,
% 0.20/0.49      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)).
% 0.20/0.49  
% 0.20/0.49  cnf(u40,axiom,
% 0.20/0.49      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)).
% 0.20/0.49  
% 0.20/0.49  cnf(u28,negated_conjecture,
% 0.20/0.49      v5_orders_2(sK0)).
% 0.20/0.49  
% 0.20/0.49  cnf(u31,axiom,
% 0.20/0.49      ~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)).
% 0.20/0.49  
% 0.20/0.49  cnf(u29,negated_conjecture,
% 0.20/0.49      v2_lattice3(sK0)).
% 0.20/0.49  
% 0.20/0.49  cnf(u30,negated_conjecture,
% 0.20/0.49      l1_orders_2(sK0)).
% 0.20/0.49  
% 0.20/0.49  % (18360)# SZS output end Saturation.
% 0.20/0.49  % (18360)------------------------------
% 0.20/0.49  % (18360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (18360)Termination reason: Satisfiable
% 0.20/0.49  
% 0.20/0.49  % (18360)Memory used [KB]: 1663
% 0.20/0.49  % (18360)Time elapsed: 0.085 s
% 0.20/0.49  % (18360)------------------------------
% 0.20/0.49  % (18360)------------------------------
% 0.20/0.49  % (18342)Success in time 0.129 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 13:17:14 EST 2020

% Result     : CounterSatisfiable 1.24s
% Output     : Saturation 1.24s
% Verified   : 
% Statistics : Number of clauses        :   20 (  20 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    0
%              Number of atoms          :   99 (  99 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal clause size      :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u22,negated_conjecture,
    ( ~ r2_hidden(k12_lattice3(sK0,sK2,sK3),sK1)
    | ~ v2_waybel_0(sK1,sK0) )).

cnf(u20,negated_conjecture,
    ( ~ v2_waybel_0(sK1,sK0)
    | r2_hidden(sK2,sK1) )).

cnf(u21,negated_conjecture,
    ( ~ v2_waybel_0(sK1,sK0)
    | r2_hidden(sK3,sK1) )).

cnf(u19,negated_conjecture,
    ( ~ v2_waybel_0(sK1,sK0)
    | m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u23,negated_conjecture,
    ( ~ v2_waybel_0(sK1,sK0)
    | m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u45,axiom,
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

cnf(u46,axiom,
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

cnf(u47,axiom,
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

cnf(u44,axiom,
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

cnf(u24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) )).

cnf(u43,axiom,
    ( ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X4,X1)
    | ~ r1_orders_2(X0,X4,X2)
    | r1_orders_2(X0,X4,k11_lattice3(X0,X1,X2)) )).

cnf(u36,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) )).

cnf(u37,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) )).

cnf(u18,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | ~ r2_hidden(X2,sK1)
    | ~ r2_hidden(X3,sK1)
    | r2_hidden(k12_lattice3(sK0,X2,X3),sK1)
    | v2_waybel_0(sK1,sK0) )).

cnf(u25,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u28,axiom,
    ( ~ v2_struct_0(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0) )).

cnf(u26,negated_conjecture,
    ( v2_lattice3(sK0) )).

cnf(u27,negated_conjecture,
    ( l1_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.36  ipcrm: permission denied for id (1219887105)
% 0.21/0.36  ipcrm: permission denied for id (1218281474)
% 0.21/0.36  ipcrm: permission denied for id (1219919875)
% 0.21/0.36  ipcrm: permission denied for id (1218314244)
% 0.21/0.36  ipcrm: permission denied for id (1219952645)
% 0.21/0.37  ipcrm: permission denied for id (1220050952)
% 0.21/0.37  ipcrm: permission denied for id (1220247565)
% 0.21/0.38  ipcrm: permission denied for id (1218412558)
% 0.21/0.38  ipcrm: permission denied for id (1218445327)
% 0.21/0.38  ipcrm: permission denied for id (1220280336)
% 0.21/0.38  ipcrm: permission denied for id (1220313105)
% 0.21/0.38  ipcrm: permission denied for id (1220345874)
% 0.21/0.38  ipcrm: permission denied for id (1220378643)
% 0.21/0.38  ipcrm: permission denied for id (1220411412)
% 0.21/0.39  ipcrm: permission denied for id (1220476950)
% 0.21/0.39  ipcrm: permission denied for id (1220542488)
% 0.21/0.39  ipcrm: permission denied for id (1218543641)
% 0.21/0.39  ipcrm: permission denied for id (1218576410)
% 0.21/0.39  ipcrm: permission denied for id (1220575259)
% 0.21/0.39  ipcrm: permission denied for id (1218609181)
% 0.21/0.40  ipcrm: permission denied for id (1220706336)
% 0.21/0.40  ipcrm: permission denied for id (1220771874)
% 0.21/0.41  ipcrm: permission denied for id (1220902950)
% 0.21/0.41  ipcrm: permission denied for id (1220935719)
% 0.21/0.41  ipcrm: permission denied for id (1220968488)
% 0.21/0.41  ipcrm: permission denied for id (1221034026)
% 0.21/0.41  ipcrm: permission denied for id (1221099563)
% 0.21/0.42  ipcrm: permission denied for id (1221132332)
% 0.21/0.42  ipcrm: permission denied for id (1221263408)
% 0.21/0.42  ipcrm: permission denied for id (1218773041)
% 0.21/0.43  ipcrm: permission denied for id (1218805813)
% 0.21/0.43  ipcrm: permission denied for id (1221394486)
% 0.21/0.43  ipcrm: permission denied for id (1218838583)
% 0.21/0.43  ipcrm: permission denied for id (1218871352)
% 0.21/0.43  ipcrm: permission denied for id (1218904121)
% 0.21/0.44  ipcrm: permission denied for id (1218969660)
% 0.21/0.44  ipcrm: permission denied for id (1219002429)
% 0.21/0.44  ipcrm: permission denied for id (1219035198)
% 0.21/0.44  ipcrm: permission denied for id (1221525568)
% 0.21/0.45  ipcrm: permission denied for id (1221689411)
% 0.21/0.45  ipcrm: permission denied for id (1221722181)
% 0.21/0.45  ipcrm: permission denied for id (1219133510)
% 0.21/0.45  ipcrm: permission denied for id (1221787720)
% 0.21/0.45  ipcrm: permission denied for id (1221853258)
% 0.21/0.46  ipcrm: permission denied for id (1221886027)
% 0.21/0.46  ipcrm: permission denied for id (1219231822)
% 0.21/0.46  ipcrm: permission denied for id (1222017104)
% 0.21/0.46  ipcrm: permission denied for id (1222049873)
% 0.21/0.46  ipcrm: permission denied for id (1222082642)
% 0.21/0.47  ipcrm: permission denied for id (1222115411)
% 0.21/0.47  ipcrm: permission denied for id (1222180949)
% 0.21/0.47  ipcrm: permission denied for id (1222246487)
% 0.21/0.47  ipcrm: permission denied for id (1222279256)
% 0.21/0.47  ipcrm: permission denied for id (1222312025)
% 0.21/0.47  ipcrm: permission denied for id (1222344794)
% 0.21/0.48  ipcrm: permission denied for id (1219428449)
% 0.21/0.49  ipcrm: permission denied for id (1222639716)
% 0.21/0.49  ipcrm: permission denied for id (1219526757)
% 0.21/0.49  ipcrm: permission denied for id (1222705255)
% 0.21/0.49  ipcrm: permission denied for id (1222803562)
% 0.21/0.50  ipcrm: permission denied for id (1222869100)
% 0.21/0.50  ipcrm: permission denied for id (1219756146)
% 0.21/0.51  ipcrm: permission denied for id (1223131253)
% 0.21/0.51  ipcrm: permission denied for id (1223164022)
% 0.21/0.51  ipcrm: permission denied for id (1223229560)
% 0.21/0.51  ipcrm: permission denied for id (1223295098)
% 0.21/0.51  ipcrm: permission denied for id (1219821691)
% 0.21/0.51  ipcrm: permission denied for id (1223327868)
% 0.21/0.52  ipcrm: permission denied for id (1223393406)
% 0.81/0.63  % (29960)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.81/0.63  % (29969)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.81/0.63  % (29973)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.81/0.64  % (29964)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.81/0.64  % (29956)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.81/0.64  % (29959)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.81/0.65  % (29962)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.24/0.66  % (29968)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 1.24/0.66  % (29967)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.24/0.66  % (29963)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.24/0.66  % (29965)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.24/0.66  % (29958)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.24/0.66  % (29955)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.24/0.66  % (29957)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.24/0.66  % (29970)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.24/0.67  % (29966)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.24/0.67  % (29966)Refutation not found, incomplete strategy% (29966)------------------------------
% 1.24/0.67  % (29966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.67  % (29966)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.67  
% 1.24/0.67  % (29966)Memory used [KB]: 6012
% 1.24/0.67  % (29966)Time elapsed: 0.003 s
% 1.24/0.67  % (29966)------------------------------
% 1.24/0.67  % (29966)------------------------------
% 1.24/0.67  % (29954)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.24/0.67  % (29955)Refutation not found, incomplete strategy% (29955)------------------------------
% 1.24/0.67  % (29955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.67  % (29955)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.67  
% 1.24/0.67  % (29955)Memory used [KB]: 10618
% 1.24/0.67  % (29955)Time elapsed: 0.082 s
% 1.24/0.67  % (29955)------------------------------
% 1.24/0.67  % (29955)------------------------------
% 1.24/0.67  % (29968)Refutation not found, incomplete strategy% (29968)------------------------------
% 1.24/0.67  % (29968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.67  % (29971)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.24/0.67  % (29968)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.67  
% 1.24/0.67  % (29968)Memory used [KB]: 10618
% 1.24/0.67  % (29968)Time elapsed: 0.104 s
% 1.24/0.67  % (29968)------------------------------
% 1.24/0.67  % (29968)------------------------------
% 1.24/0.67  % (29972)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.24/0.67  % SZS status CounterSatisfiable for theBenchmark
% 1.24/0.67  % (29971)# SZS output start Saturation.
% 1.24/0.67  cnf(u22,negated_conjecture,
% 1.24/0.67      ~r2_hidden(k12_lattice3(sK0,sK2,sK3),sK1) | ~v2_waybel_0(sK1,sK0)).
% 1.24/0.67  
% 1.24/0.67  cnf(u20,negated_conjecture,
% 1.24/0.67      ~v2_waybel_0(sK1,sK0) | r2_hidden(sK2,sK1)).
% 1.24/0.67  
% 1.24/0.67  cnf(u21,negated_conjecture,
% 1.24/0.67      ~v2_waybel_0(sK1,sK0) | r2_hidden(sK3,sK1)).
% 1.24/0.67  
% 1.24/0.67  cnf(u19,negated_conjecture,
% 1.24/0.67      ~v2_waybel_0(sK1,sK0) | m1_subset_1(sK3,u1_struct_0(sK0))).
% 1.24/0.67  
% 1.24/0.67  cnf(u23,negated_conjecture,
% 1.24/0.67      ~v2_waybel_0(sK1,sK0) | m1_subset_1(sK2,u1_struct_0(sK0))).
% 1.24/0.67  
% 1.24/0.67  cnf(u45,axiom,
% 1.24/0.67      ~r1_orders_2(X0,X3,X1) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK4(X0,X1,X2,X3),X2) | k11_lattice3(X0,X1,X2) = X3).
% 1.24/0.67  
% 1.24/0.67  cnf(u46,axiom,
% 1.24/0.67      ~r1_orders_2(X0,X3,X1) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK4(X0,X1,X2,X3),X1) | k11_lattice3(X0,X1,X2) = X3).
% 1.24/0.67  
% 1.24/0.67  cnf(u47,axiom,
% 1.24/0.67      ~r1_orders_2(X0,X3,X1) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = X3).
% 1.24/0.67  
% 1.24/0.67  cnf(u44,axiom,
% 1.24/0.67      ~r1_orders_2(X0,sK4(X0,X1,X2,X3),X3) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | ~v5_orders_2(X0) | k11_lattice3(X0,X1,X2) = X3).
% 1.24/0.67  
% 1.24/0.67  cnf(u24,negated_conjecture,
% 1.24/0.67      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.24/0.67  
% 1.24/0.67  cnf(u41,axiom,
% 1.24/0.67      ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)).
% 1.24/0.67  
% 1.24/0.67  cnf(u42,axiom,
% 1.24/0.67      ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)).
% 1.24/0.67  
% 1.24/0.67  cnf(u43,axiom,
% 1.24/0.67      ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_orders_2(X0,X4,X1) | ~r1_orders_2(X0,X4,X2) | r1_orders_2(X0,X4,k11_lattice3(X0,X1,X2))).
% 1.24/0.67  
% 1.24/0.67  cnf(u36,axiom,
% 1.24/0.67      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))).
% 1.24/0.67  
% 1.24/0.67  cnf(u37,axiom,
% 1.24/0.67      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)).
% 1.24/0.67  
% 1.24/0.67  cnf(u18,negated_conjecture,
% 1.24/0.67      ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | ~r2_hidden(X3,sK1) | r2_hidden(k12_lattice3(sK0,X2,X3),sK1) | v2_waybel_0(sK1,sK0)).
% 1.24/0.67  
% 1.24/0.67  cnf(u25,negated_conjecture,
% 1.24/0.67      v5_orders_2(sK0)).
% 1.24/0.67  
% 1.24/0.67  cnf(u28,axiom,
% 1.24/0.67      ~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)).
% 1.24/0.67  
% 1.24/0.67  cnf(u26,negated_conjecture,
% 1.24/0.67      v2_lattice3(sK0)).
% 1.24/0.67  
% 1.24/0.67  cnf(u27,negated_conjecture,
% 1.24/0.67      l1_orders_2(sK0)).
% 1.24/0.67  
% 1.24/0.67  % (29971)# SZS output end Saturation.
% 1.24/0.67  % (29971)------------------------------
% 1.24/0.67  % (29971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.67  % (29971)Termination reason: Satisfiable
% 1.24/0.67  
% 1.24/0.67  % (29971)Memory used [KB]: 1663
% 1.24/0.67  % (29971)Time elapsed: 0.101 s
% 1.24/0.67  % (29971)------------------------------
% 1.24/0.67  % (29971)------------------------------
% 1.24/0.67  % (29788)Success in time 0.319 s
%------------------------------------------------------------------------------

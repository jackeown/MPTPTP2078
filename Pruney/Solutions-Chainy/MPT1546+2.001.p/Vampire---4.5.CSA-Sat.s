%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:00 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   52 (  52 expanded)
%              Number of leaves         :   52 (  52 expanded)
%              Depth                    :    0
%              Number of atoms          :  144 ( 144 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    5 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u34,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u35,negated_conjecture,
    ( v1_lattice3(sK0) )).

cnf(u42,axiom,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0) )).

cnf(u106,axiom,
    ( r1_orders_2(X0,sK3(X1,u1_struct_0(X0)),sK3(X1,u1_struct_0(X0)))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ v1_relat_1(X1)
    | r1_relat_2(X1,u1_struct_0(X0)) )).

cnf(u107,axiom,
    ( r1_orders_2(X2,sK4(u1_struct_0(X2)),sK4(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2)
    | v1_xboole_0(u1_struct_0(X2)) )).

cnf(u111,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK2)
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u109,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1)
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u29,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK1)
    | sK1 = k13_lattice3(sK0,sK1,sK2) )).

cnf(u118,axiom,
    ( ~ r1_orders_2(X3,sK3(u1_orders_2(X3),X4),sK3(u1_orders_2(X3),X4))
    | ~ l1_orders_2(X3)
    | ~ m1_subset_1(sK3(u1_orders_2(X3),X4),u1_struct_0(X3))
    | r1_relat_2(u1_orders_2(X3),X4) )).

cnf(u115,axiom,
    ( ~ r1_orders_2(X9,X8,X10)
    | ~ m1_subset_1(X10,u1_struct_0(X9))
    | ~ l1_orders_2(X9)
    | ~ m1_subset_1(X8,u1_struct_0(X9))
    | ~ v1_xboole_0(u1_orders_2(X9)) )).

cnf(u33,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u36,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u40,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u53,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u55,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u88,axiom,
    ( r1_relat_2(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v1_xboole_0(u1_orders_2(X0))
    | ~ v1_relat_1(X1)
    | ~ l1_orders_2(X0) )).

cnf(u70,axiom,
    ( r1_relat_2(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_xboole_0(X3) )).

cnf(u44,axiom,
    ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) )).

cnf(u37,axiom,
    ( ~ r1_relat_2(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X2,X2),X0)
    | ~ v1_relat_1(X0) )).

cnf(u43,axiom,
    ( ~ r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v3_orders_2(X0) )).

cnf(u73,axiom,
    ( v1_relat_1(sK3(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | ~ v1_relat_1(X2)
    | r1_relat_2(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )).

cnf(u66,axiom,
    ( v1_relat_1(sK4(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )).

cnf(u74,axiom,
    ( v1_relat_1(u1_orders_2(X0))
    | ~ l1_orders_2(X0) )).

cnf(u114,axiom,
    ( m1_subset_1(k4_tarski(X5,X7),u1_orders_2(X6))
    | ~ m1_subset_1(X7,u1_struct_0(X6))
    | ~ l1_orders_2(X6)
    | ~ r1_orders_2(X6,X5,X7)
    | ~ m1_subset_1(X5,u1_struct_0(X6)) )).

cnf(u83,axiom,
    ( m1_subset_1(k4_tarski(X2,X2),u1_orders_2(X3))
    | ~ l1_orders_2(X3)
    | ~ v3_orders_2(X3)
    | ~ r2_hidden(X2,u1_struct_0(X3)) )).

cnf(u32,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u31,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u41,axiom,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) )).

cnf(u69,axiom,
    ( m1_subset_1(sK3(X0,X1),X1)
    | r1_relat_2(X0,X1)
    | ~ v1_relat_1(X0) )).

cnf(u57,axiom,
    ( m1_subset_1(sK4(X0),X0)
    | v1_xboole_0(X0) )).

cnf(u52,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(X2) )).

cnf(u51,axiom,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | r2_hidden(X0,X1) )).

cnf(u48,axiom,
    ( r2_hidden(sK4(X0),X0)
    | v1_xboole_0(X0) )).

cnf(u38,axiom,
    ( r2_hidden(sK3(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | r1_relat_2(X0,X1) )).

cnf(u58,negated_conjecture,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u59,negated_conjecture,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u75,axiom,
    ( r2_hidden(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) )).

cnf(u46,axiom,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ r1_orders_2(X0,X1,X2) )).

cnf(u81,axiom,
    ( r2_hidden(k4_tarski(X0,X0),u1_orders_2(X1))
    | ~ r2_hidden(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) )).

cnf(u85,axiom,
    ( ~ r2_hidden(sK3(u1_orders_2(X0),X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | r1_relat_2(u1_orders_2(X0),X1) )).

cnf(u45,axiom,
    ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_orders_2(X0,X1,X2) )).

cnf(u39,axiom,
    ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X0)
    | ~ v1_relat_1(X0)
    | r1_relat_2(X0,X1) )).

cnf(u84,axiom,
    ( ~ r2_hidden(X4,u1_struct_0(X5))
    | ~ l1_orders_2(X5)
    | ~ v3_orders_2(X5)
    | ~ v1_xboole_0(u1_orders_2(X5)) )).

cnf(u103,axiom,
    ( ~ r2_hidden(X0,u1_struct_0(X1))
    | r1_orders_2(X1,X0,X0)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) )).

cnf(u49,axiom,
    ( ~ r2_hidden(X1,X0)
    | ~ v1_xboole_0(X0) )).

cnf(u50,axiom,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) )).

cnf(u89,axiom,
    ( ~ v1_xboole_0(u1_orders_2(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2)
    | v1_xboole_0(u1_struct_0(X2)) )).

cnf(u91,negated_conjecture,
    ( ~ v1_xboole_0(u1_orders_2(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u128,negated_conjecture,
    ( ~ v1_xboole_0(u1_orders_2(sK0))
    | sK1 = k13_lattice3(sK0,sK1,sK2) )).

cnf(u47,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u77,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v3_orders_2(X0) )).

cnf(u30,negated_conjecture,
    ( sK1 != k13_lattice3(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK2,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:08:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (3734)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.46  % (3726)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.47  % (3722)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.47  % (3723)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.48  % (3715)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.48  % (3719)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.48  % (3718)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.49  % (3735)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.49  % (3725)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.49  % (3724)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.49  % (3724)Refutation not found, incomplete strategy% (3724)------------------------------
% 0.20/0.49  % (3724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (3724)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (3724)Memory used [KB]: 10618
% 0.20/0.49  % (3724)Time elapsed: 0.084 s
% 0.20/0.49  % (3724)------------------------------
% 0.20/0.49  % (3724)------------------------------
% 0.20/0.49  % (3722)Refutation not found, incomplete strategy% (3722)------------------------------
% 0.20/0.49  % (3722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (3722)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (3722)Memory used [KB]: 10618
% 0.20/0.49  % (3722)Time elapsed: 0.087 s
% 0.20/0.49  % (3722)------------------------------
% 0.20/0.49  % (3722)------------------------------
% 0.20/0.49  % (3717)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (3717)Refutation not found, incomplete strategy% (3717)------------------------------
% 0.20/0.50  % (3717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3717)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3717)Memory used [KB]: 10618
% 0.20/0.50  % (3717)Time elapsed: 0.084 s
% 0.20/0.50  % (3717)------------------------------
% 0.20/0.50  % (3717)------------------------------
% 0.20/0.50  % (3729)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.50  % (3716)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (3737)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.50  % (3731)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.50  % (3737)Refutation not found, incomplete strategy% (3737)------------------------------
% 0.20/0.50  % (3737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3737)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3737)Memory used [KB]: 10618
% 0.20/0.50  % (3737)Time elapsed: 0.099 s
% 0.20/0.50  % (3737)------------------------------
% 0.20/0.50  % (3737)------------------------------
% 0.20/0.50  % (3733)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.50  % (3731)Refutation not found, incomplete strategy% (3731)------------------------------
% 0.20/0.50  % (3731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3731)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3731)Memory used [KB]: 1663
% 0.20/0.50  % (3731)Time elapsed: 0.065 s
% 0.20/0.50  % (3731)------------------------------
% 0.20/0.50  % (3731)------------------------------
% 0.20/0.51  % (3716)Refutation not found, incomplete strategy% (3716)------------------------------
% 0.20/0.51  % (3716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3716)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (3716)Memory used [KB]: 10618
% 0.20/0.51  % (3716)Time elapsed: 0.097 s
% 0.20/0.51  % (3716)------------------------------
% 0.20/0.51  % (3716)------------------------------
% 0.20/0.51  % (3730)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.51  % (3728)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.51  % (3730)Refutation not found, incomplete strategy% (3730)------------------------------
% 0.20/0.51  % (3730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3730)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (3730)Memory used [KB]: 1663
% 0.20/0.51  % (3730)Time elapsed: 0.116 s
% 0.20/0.51  % (3730)------------------------------
% 0.20/0.51  % (3730)------------------------------
% 0.20/0.51  % (3736)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.51  % (3714)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.51  % (3720)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.51  % (3733)Refutation not found, incomplete strategy% (3733)------------------------------
% 0.20/0.51  % (3733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3733)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (3733)Memory used [KB]: 6140
% 0.20/0.51  % (3733)Time elapsed: 0.111 s
% 0.20/0.51  % (3733)------------------------------
% 0.20/0.51  % (3733)------------------------------
% 0.20/0.51  % (3720)Refutation not found, incomplete strategy% (3720)------------------------------
% 0.20/0.51  % (3720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3732)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.52  % (3721)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (3721)Refutation not found, incomplete strategy% (3721)------------------------------
% 0.20/0.52  % (3721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (3721)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (3721)Memory used [KB]: 6140
% 0.20/0.52  % (3721)Time elapsed: 0.120 s
% 0.20/0.52  % (3721)------------------------------
% 0.20/0.52  % (3721)------------------------------
% 0.20/0.53  % (3720)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (3720)Memory used [KB]: 10618
% 0.20/0.53  % (3720)Time elapsed: 0.080 s
% 0.20/0.53  % (3720)------------------------------
% 0.20/0.53  % (3720)------------------------------
% 0.20/0.53  % (3727)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.53  % (3727)# SZS output start Saturation.
% 0.20/0.53  cnf(u34,negated_conjecture,
% 0.20/0.53      v5_orders_2(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u35,negated_conjecture,
% 0.20/0.53      v1_lattice3(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u42,axiom,
% 0.20/0.53      ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v2_struct_0(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u106,axiom,
% 0.20/0.53      r1_orders_2(X0,sK3(X1,u1_struct_0(X0)),sK3(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v1_relat_1(X1) | r1_relat_2(X1,u1_struct_0(X0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u107,axiom,
% 0.20/0.53      r1_orders_2(X2,sK4(u1_struct_0(X2)),sK4(u1_struct_0(X2))) | ~l1_orders_2(X2) | ~v3_orders_2(X2) | v1_xboole_0(u1_struct_0(X2))).
% 0.20/0.53  
% 0.20/0.53  cnf(u111,negated_conjecture,
% 0.20/0.53      r1_orders_2(sK0,sK2,sK2) | v1_xboole_0(u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u109,negated_conjecture,
% 0.20/0.53      r1_orders_2(sK0,sK1,sK1) | v1_xboole_0(u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u29,negated_conjecture,
% 0.20/0.53      r1_orders_2(sK0,sK2,sK1) | sK1 = k13_lattice3(sK0,sK1,sK2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u118,axiom,
% 0.20/0.53      ~r1_orders_2(X3,sK3(u1_orders_2(X3),X4),sK3(u1_orders_2(X3),X4)) | ~l1_orders_2(X3) | ~m1_subset_1(sK3(u1_orders_2(X3),X4),u1_struct_0(X3)) | r1_relat_2(u1_orders_2(X3),X4)).
% 0.20/0.53  
% 0.20/0.53  cnf(u115,axiom,
% 0.20/0.53      ~r1_orders_2(X9,X8,X10) | ~m1_subset_1(X10,u1_struct_0(X9)) | ~l1_orders_2(X9) | ~m1_subset_1(X8,u1_struct_0(X9)) | ~v1_xboole_0(u1_orders_2(X9))).
% 0.20/0.53  
% 0.20/0.53  cnf(u33,negated_conjecture,
% 0.20/0.53      v3_orders_2(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u36,negated_conjecture,
% 0.20/0.53      l1_orders_2(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u40,axiom,
% 0.20/0.53      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u53,negated_conjecture,
% 0.20/0.53      l1_struct_0(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u55,negated_conjecture,
% 0.20/0.53      ~v2_struct_0(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u88,axiom,
% 0.20/0.53      r1_relat_2(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v1_xboole_0(u1_orders_2(X0)) | ~v1_relat_1(X1) | ~l1_orders_2(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u70,axiom,
% 0.20/0.53      r1_relat_2(X2,X3) | ~v1_relat_1(X2) | ~v1_xboole_0(X3)).
% 0.20/0.53  
% 0.20/0.53  cnf(u44,axiom,
% 0.20/0.53      r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u37,axiom,
% 0.20/0.53      ~r1_relat_2(X0,X1) | ~r2_hidden(X2,X1) | r2_hidden(k4_tarski(X2,X2),X0) | ~v1_relat_1(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u43,axiom,
% 0.20/0.53      ~r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~l1_orders_2(X0) | v3_orders_2(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u73,axiom,
% 0.20/0.53      v1_relat_1(sK3(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) | ~v1_relat_1(X2) | r1_relat_2(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))).
% 0.20/0.53  
% 0.20/0.53  cnf(u66,axiom,
% 0.20/0.53      v1_relat_1(sK4(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))).
% 0.20/0.53  
% 0.20/0.53  cnf(u74,axiom,
% 0.20/0.53      v1_relat_1(u1_orders_2(X0)) | ~l1_orders_2(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u114,axiom,
% 0.20/0.53      m1_subset_1(k4_tarski(X5,X7),u1_orders_2(X6)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l1_orders_2(X6) | ~r1_orders_2(X6,X5,X7) | ~m1_subset_1(X5,u1_struct_0(X6))).
% 0.20/0.53  
% 0.20/0.53  cnf(u83,axiom,
% 0.20/0.53      m1_subset_1(k4_tarski(X2,X2),u1_orders_2(X3)) | ~l1_orders_2(X3) | ~v3_orders_2(X3) | ~r2_hidden(X2,u1_struct_0(X3))).
% 0.20/0.53  
% 0.20/0.53  cnf(u32,negated_conjecture,
% 0.20/0.53      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u31,negated_conjecture,
% 0.20/0.53      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u41,axiom,
% 0.20/0.53      m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u69,axiom,
% 0.20/0.53      m1_subset_1(sK3(X0,X1),X1) | r1_relat_2(X0,X1) | ~v1_relat_1(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u57,axiom,
% 0.20/0.53      m1_subset_1(sK4(X0),X0) | v1_xboole_0(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u52,axiom,
% 0.20/0.53      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u51,axiom,
% 0.20/0.53      ~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u48,axiom,
% 0.20/0.53      r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u38,axiom,
% 0.20/0.53      r2_hidden(sK3(X0,X1),X1) | ~v1_relat_1(X0) | r1_relat_2(X0,X1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u58,negated_conjecture,
% 0.20/0.53      r2_hidden(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u59,negated_conjecture,
% 0.20/0.53      r2_hidden(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u75,axiom,
% 0.20/0.53      r2_hidden(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) | ~l1_orders_2(X1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u46,axiom,
% 0.20/0.53      r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u81,axiom,
% 0.20/0.53      r2_hidden(k4_tarski(X0,X0),u1_orders_2(X1)) | ~r2_hidden(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v3_orders_2(X1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u85,axiom,
% 0.20/0.53      ~r2_hidden(sK3(u1_orders_2(X0),X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | r1_relat_2(u1_orders_2(X0),X1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u45,axiom,
% 0.20/0.53      ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u39,axiom,
% 0.20/0.53      ~r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X0) | ~v1_relat_1(X0) | r1_relat_2(X0,X1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u84,axiom,
% 0.20/0.53      ~r2_hidden(X4,u1_struct_0(X5)) | ~l1_orders_2(X5) | ~v3_orders_2(X5) | ~v1_xboole_0(u1_orders_2(X5))).
% 0.20/0.53  
% 0.20/0.53  cnf(u103,axiom,
% 0.20/0.53      ~r2_hidden(X0,u1_struct_0(X1)) | r1_orders_2(X1,X0,X0) | ~l1_orders_2(X1) | ~v3_orders_2(X1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u49,axiom,
% 0.20/0.53      ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u50,axiom,
% 0.20/0.53      ~r2_hidden(X0,X1) | m1_subset_1(X0,X1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u89,axiom,
% 0.20/0.53      ~v1_xboole_0(u1_orders_2(X2)) | ~v3_orders_2(X2) | ~l1_orders_2(X2) | v1_xboole_0(u1_struct_0(X2))).
% 0.20/0.53  
% 0.20/0.53  cnf(u91,negated_conjecture,
% 0.20/0.53      ~v1_xboole_0(u1_orders_2(sK0)) | v1_xboole_0(u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u128,negated_conjecture,
% 0.20/0.53      ~v1_xboole_0(u1_orders_2(sK0)) | sK1 = k13_lattice3(sK0,sK1,sK2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u47,axiom,
% 0.20/0.53      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u77,axiom,
% 0.20/0.53      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_orders_2(X0) | v3_orders_2(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u30,negated_conjecture,
% 0.20/0.53      sK1 != k13_lattice3(sK0,sK1,sK2) | ~r1_orders_2(sK0,sK2,sK1)).
% 0.20/0.53  
% 0.20/0.53  % (3727)# SZS output end Saturation.
% 0.20/0.53  % (3727)------------------------------
% 0.20/0.53  % (3727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3727)Termination reason: Satisfiable
% 0.20/0.53  
% 0.20/0.53  % (3727)Memory used [KB]: 6140
% 0.20/0.53  % (3727)Time elapsed: 0.107 s
% 0.20/0.53  % (3727)------------------------------
% 0.20/0.53  % (3727)------------------------------
% 0.20/0.53  % (3713)Success in time 0.178 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:19 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   45 (  45 expanded)
%              Number of leaves         :   45 (  45 expanded)
%              Depth                    :    0
%              Number of atoms          :  180 ( 180 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal clause size      :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u49,negated_conjecture,
    ( ~ v2_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,sK0)
    | ~ v5_yellow_0(k5_yellow_0(sK0,sK1),sK0)
    | v1_xboole_0(sK1) )).

cnf(u43,negated_conjecture,
    ( v13_waybel_0(sK1,sK0) )).

cnf(u38,negated_conjecture,
    ( v4_orders_2(sK0) )).

cnf(u58,axiom,
    ( ~ v4_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2)
    | ~ v3_orders_2(X0) )).

cnf(u37,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u78,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0)) = k12_lattice3(sK0,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u39,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u79,negated_conjecture,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k12_lattice3(sK0,X0,X1) = k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK0)) )).

cnf(u59,axiom,
    ( ~ v5_orders_2(X0)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | r2_yellow_0(X0,k2_tarski(X3,X4)) )).

cnf(u68,axiom,
    ( ~ v5_orders_2(X8)
    | k7_domain_1(u1_struct_0(X8),sK4(X8),X7) = k2_tarski(sK4(X8),X7)
    | v1_xboole_0(u1_struct_0(X8))
    | v2_lattice3(X8)
    | ~ l1_orders_2(X8)
    | ~ m1_subset_1(X7,u1_struct_0(X8)) )).

cnf(u69,axiom,
    ( ~ v5_orders_2(X10)
    | k7_domain_1(u1_struct_0(X10),sK5(X10),X9) = k2_tarski(sK5(X10),X9)
    | v1_xboole_0(u1_struct_0(X10))
    | v2_lattice3(X10)
    | ~ l1_orders_2(X10)
    | ~ m1_subset_1(X9,u1_struct_0(X10)) )).

cnf(u56,axiom,
    ( r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK2(X0,X1),sK3(X0,X1)))
    | v5_yellow_0(X1,X0)
    | ~ m1_yellow_0(X1,X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u74,negated_conjecture,
    ( r2_yellow_0(sK0,k2_tarski(X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u62,axiom,
    ( ~ r2_yellow_0(X0,k2_tarski(sK4(X0),sK5(X0)))
    | v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) )).

cnf(u45,negated_conjecture,
    ( v5_yellow_0(k5_yellow_0(sK0,sK1),sK0)
    | ~ v1_xboole_0(sK1) )).

cnf(u46,negated_conjecture,
    ( v5_yellow_0(k5_yellow_0(sK0,sK1),sK0)
    | v2_waybel_0(sK1,sK0) )).

cnf(u47,negated_conjecture,
    ( v5_yellow_0(k5_yellow_0(sK0,sK1),sK0)
    | v13_waybel_0(sK1,sK0) )).

cnf(u48,negated_conjecture,
    ( v5_yellow_0(k5_yellow_0(sK0,sK1),sK0)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u83,negated_conjecture,
    ( ~ m1_yellow_0(X1,sK0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | v5_yellow_0(X1,sK0)
    | k12_lattice3(sK0,X0,sK2(sK0,X1)) = k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X0,sK2(sK0,X1)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) )).

cnf(u84,negated_conjecture,
    ( ~ m1_yellow_0(X3,sK0)
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | v5_yellow_0(X3,sK0)
    | k12_lattice3(sK0,X2,sK3(sK0,X3)) = k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X2,sK3(sK0,X3)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) )).

cnf(u51,axiom,
    ( ~ m1_yellow_0(X1,X0)
    | ~ r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5))
    | ~ r2_hidden(X5,u1_struct_0(X1))
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v5_yellow_0(X1,X0)
    | r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5)),u1_struct_0(X1))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u66,axiom,
    ( ~ m1_yellow_0(X3,X2)
    | k7_domain_1(u1_struct_0(X2),sK2(X2,X3),X1) = k2_tarski(sK2(X2,X3),X1)
    | v1_xboole_0(u1_struct_0(X2))
    | v5_yellow_0(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | v2_struct_0(X2) )).

cnf(u67,axiom,
    ( ~ m1_yellow_0(X6,X5)
    | k7_domain_1(u1_struct_0(X5),sK3(X5,X6),X4) = k2_tarski(sK3(X5,X6),X4)
    | v1_xboole_0(u1_struct_0(X5))
    | v5_yellow_0(X6,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ l1_orders_2(X5)
    | v2_struct_0(X5) )).

cnf(u50,axiom,
    ( ~ v2_struct_0(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0) )).

cnf(u40,negated_conjecture,
    ( v2_lattice3(sK0) )).

cnf(u72,negated_conjecture,
    ( ~ v2_lattice3(sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_yellow_0(sK0,k2_tarski(X1,X0)) )).

cnf(u80,negated_conjecture,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k12_lattice3(sK0,X0,X1) = k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK0)) )).

cnf(u41,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u73,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r2_yellow_0(sK0,k2_tarski(X0,X1)) )).

cnf(u81,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k12_lattice3(sK0,X0,X1) = k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK0)) )).

cnf(u70,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK1) = k2_tarski(sK1,sK1) )).

cnf(u64,axiom,
    ( ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X0,X1) )).

cnf(u42,negated_conjecture,
    ( ~ v1_xboole_0(sK1) )).

cnf(u61,axiom,
    ( m1_subset_1(sK5(X0),u1_struct_0(X0))
    | v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) )).

cnf(u60,axiom,
    ( m1_subset_1(sK4(X0),u1_struct_0(X0))
    | v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) )).

cnf(u53,axiom,
    ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
    | v5_yellow_0(X1,X0)
    | ~ m1_yellow_0(X1,X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u52,axiom,
    ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
    | v5_yellow_0(X1,X0)
    | ~ m1_yellow_0(X1,X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u44,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u82,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k12_lattice3(sK0,X0,X1) = k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u71,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK1) = k2_tarski(sK1,sK1)
    | ~ r2_hidden(X1,X0) )).

cnf(u65,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k2_tarski(sK1,X0)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u63,axiom,
    ( ~ m1_subset_1(X1,X0)
    | ~ m1_subset_1(X2,X0)
    | k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
    | v1_xboole_0(X0) )).

cnf(u55,axiom,
    ( r2_hidden(sK3(X0,X1),u1_struct_0(X1))
    | v5_yellow_0(X1,X0)
    | ~ m1_yellow_0(X1,X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u54,axiom,
    ( r2_hidden(sK2(X0,X1),u1_struct_0(X1))
    | v5_yellow_0(X1,X0)
    | ~ m1_yellow_0(X1,X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u57,axiom,
    ( ~ r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK2(X0,X1),sK3(X0,X1))),u1_struct_0(X1))
    | v5_yellow_0(X1,X0)
    | ~ m1_yellow_0(X1,X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:37:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (3725)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (3725)Refutation not found, incomplete strategy% (3725)------------------------------
% 0.22/0.52  % (3725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3725)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (3725)Memory used [KB]: 10618
% 0.22/0.52  % (3725)Time elapsed: 0.072 s
% 0.22/0.52  % (3725)------------------------------
% 0.22/0.52  % (3725)------------------------------
% 0.22/0.52  % (3733)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.52  % (3733)Refutation not found, incomplete strategy% (3733)------------------------------
% 0.22/0.52  % (3733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3733)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (3733)Memory used [KB]: 1535
% 0.22/0.52  % (3733)Time elapsed: 0.072 s
% 0.22/0.52  % (3733)------------------------------
% 0.22/0.52  % (3733)------------------------------
% 0.22/0.55  % (3717)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.56  % (3720)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.56  % (3720)Refutation not found, incomplete strategy% (3720)------------------------------
% 0.22/0.56  % (3720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (3720)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (3720)Memory used [KB]: 10618
% 0.22/0.56  % (3720)Time elapsed: 0.121 s
% 0.22/0.56  % (3720)------------------------------
% 0.22/0.56  % (3720)------------------------------
% 0.22/0.56  % (3721)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.56  % (3722)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.57  % (3737)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.57  % (3740)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.57  % (3737)Refutation not found, incomplete strategy% (3737)------------------------------
% 0.22/0.57  % (3737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (3737)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (3737)Memory used [KB]: 6140
% 0.22/0.57  % (3737)Time elapsed: 0.133 s
% 0.22/0.57  % (3737)------------------------------
% 0.22/0.57  % (3737)------------------------------
% 0.22/0.57  % (3730)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.57  % (3735)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.57  % (3724)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.57  % (3728)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.58  % (3724)Refutation not found, incomplete strategy% (3724)------------------------------
% 0.22/0.58  % (3724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (3724)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (3724)Memory used [KB]: 6140
% 0.22/0.58  % (3724)Time elapsed: 0.138 s
% 0.22/0.58  % (3724)------------------------------
% 0.22/0.58  % (3724)------------------------------
% 0.22/0.58  % (3719)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.58  % (3728)Refutation not found, incomplete strategy% (3728)------------------------------
% 0.22/0.58  % (3728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (3728)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (3728)Memory used [KB]: 1663
% 0.22/0.58  % (3728)Time elapsed: 0.143 s
% 0.22/0.58  % (3728)------------------------------
% 0.22/0.58  % (3728)------------------------------
% 0.22/0.58  % (3718)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.58  % (3729)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.58  % (3719)Refutation not found, incomplete strategy% (3719)------------------------------
% 0.22/0.58  % (3719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (3719)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (3719)Memory used [KB]: 10618
% 0.22/0.58  % (3719)Time elapsed: 0.138 s
% 0.22/0.58  % (3719)------------------------------
% 0.22/0.58  % (3719)------------------------------
% 0.22/0.58  % (3736)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.58  % (3738)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.58  % (3736)Refutation not found, incomplete strategy% (3736)------------------------------
% 0.22/0.58  % (3736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (3736)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (3736)Memory used [KB]: 6140
% 0.22/0.58  % (3736)Time elapsed: 0.141 s
% 0.22/0.58  % (3736)------------------------------
% 0.22/0.58  % (3736)------------------------------
% 0.22/0.58  % (3732)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.58  % (3738)Refutation not found, incomplete strategy% (3738)------------------------------
% 0.22/0.58  % (3738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (3738)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (3738)Memory used [KB]: 1663
% 0.22/0.58  % (3738)Time elapsed: 0.143 s
% 0.22/0.58  % (3738)------------------------------
% 0.22/0.58  % (3738)------------------------------
% 0.22/0.58  % (3727)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.59  % (3734)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.59  % (3727)Refutation not found, incomplete strategy% (3727)------------------------------
% 0.22/0.59  % (3727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (3727)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (3727)Memory used [KB]: 10490
% 0.22/0.59  % (3727)Time elapsed: 0.151 s
% 0.22/0.59  % (3727)------------------------------
% 0.22/0.59  % (3727)------------------------------
% 0.22/0.59  % (3726)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.59  % (3740)Refutation not found, incomplete strategy% (3740)------------------------------
% 0.22/0.59  % (3740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (3740)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (3740)Memory used [KB]: 10618
% 0.22/0.59  % (3740)Time elapsed: 0.150 s
% 0.22/0.59  % (3740)------------------------------
% 0.22/0.59  % (3740)------------------------------
% 0.22/0.59  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.59  % (3726)# SZS output start Saturation.
% 0.22/0.59  cnf(u49,negated_conjecture,
% 0.22/0.59      ~v2_waybel_0(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v13_waybel_0(sK1,sK0) | ~v5_yellow_0(k5_yellow_0(sK0,sK1),sK0) | v1_xboole_0(sK1)).
% 0.22/0.59  
% 0.22/0.59  cnf(u43,negated_conjecture,
% 0.22/0.59      v13_waybel_0(sK1,sK0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u38,negated_conjecture,
% 0.22/0.59      v4_orders_2(sK0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u58,axiom,
% 0.22/0.59      ~v4_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2) | ~v3_orders_2(X0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u37,negated_conjecture,
% 0.22/0.59      v3_orders_2(sK0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u78,negated_conjecture,
% 0.22/0.59      ~v3_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0)) = k12_lattice3(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 0.22/0.59  
% 0.22/0.59  cnf(u39,negated_conjecture,
% 0.22/0.59      v5_orders_2(sK0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u79,negated_conjecture,
% 0.22/0.59      ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k12_lattice3(sK0,X0,X1) = k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0))).
% 0.22/0.59  
% 0.22/0.59  cnf(u59,axiom,
% 0.22/0.59      ~v5_orders_2(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | r2_yellow_0(X0,k2_tarski(X3,X4))).
% 0.22/0.59  
% 0.22/0.59  cnf(u68,axiom,
% 0.22/0.59      ~v5_orders_2(X8) | k7_domain_1(u1_struct_0(X8),sK4(X8),X7) = k2_tarski(sK4(X8),X7) | v1_xboole_0(u1_struct_0(X8)) | v2_lattice3(X8) | ~l1_orders_2(X8) | ~m1_subset_1(X7,u1_struct_0(X8))).
% 0.22/0.59  
% 0.22/0.59  cnf(u69,axiom,
% 0.22/0.59      ~v5_orders_2(X10) | k7_domain_1(u1_struct_0(X10),sK5(X10),X9) = k2_tarski(sK5(X10),X9) | v1_xboole_0(u1_struct_0(X10)) | v2_lattice3(X10) | ~l1_orders_2(X10) | ~m1_subset_1(X9,u1_struct_0(X10))).
% 0.22/0.59  
% 0.22/0.59  cnf(u56,axiom,
% 0.22/0.59      r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK2(X0,X1),sK3(X0,X1))) | v5_yellow_0(X1,X0) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u74,negated_conjecture,
% 0.22/0.59      r2_yellow_0(sK0,k2_tarski(X1,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 0.22/0.59  
% 0.22/0.59  cnf(u62,axiom,
% 0.22/0.59      ~r2_yellow_0(X0,k2_tarski(sK4(X0),sK5(X0))) | v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u45,negated_conjecture,
% 0.22/0.59      v5_yellow_0(k5_yellow_0(sK0,sK1),sK0) | ~v1_xboole_0(sK1)).
% 0.22/0.59  
% 0.22/0.59  cnf(u46,negated_conjecture,
% 0.22/0.59      v5_yellow_0(k5_yellow_0(sK0,sK1),sK0) | v2_waybel_0(sK1,sK0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u47,negated_conjecture,
% 0.22/0.59      v5_yellow_0(k5_yellow_0(sK0,sK1),sK0) | v13_waybel_0(sK1,sK0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u48,negated_conjecture,
% 0.22/0.59      v5_yellow_0(k5_yellow_0(sK0,sK1),sK0) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.59  
% 0.22/0.59  cnf(u83,negated_conjecture,
% 0.22/0.59      ~m1_yellow_0(X1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v5_yellow_0(X1,sK0) | k12_lattice3(sK0,X0,sK2(sK0,X1)) = k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X0,sK2(sK0,X1))) | ~l1_orders_2(sK0) | v2_struct_0(sK0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u84,negated_conjecture,
% 0.22/0.59      ~m1_yellow_0(X3,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v5_yellow_0(X3,sK0) | k12_lattice3(sK0,X2,sK3(sK0,X3)) = k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X2,sK3(sK0,X3))) | ~l1_orders_2(sK0) | v2_struct_0(sK0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u51,axiom,
% 0.22/0.59      ~m1_yellow_0(X1,X0) | ~r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5)) | ~r2_hidden(X5,u1_struct_0(X1)) | ~r2_hidden(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v5_yellow_0(X1,X0) | r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5)),u1_struct_0(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u66,axiom,
% 0.22/0.59      ~m1_yellow_0(X3,X2) | k7_domain_1(u1_struct_0(X2),sK2(X2,X3),X1) = k2_tarski(sK2(X2,X3),X1) | v1_xboole_0(u1_struct_0(X2)) | v5_yellow_0(X3,X2) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~l1_orders_2(X2) | v2_struct_0(X2)).
% 0.22/0.59  
% 0.22/0.59  cnf(u67,axiom,
% 0.22/0.59      ~m1_yellow_0(X6,X5) | k7_domain_1(u1_struct_0(X5),sK3(X5,X6),X4) = k2_tarski(sK3(X5,X6),X4) | v1_xboole_0(u1_struct_0(X5)) | v5_yellow_0(X6,X5) | ~m1_subset_1(X4,u1_struct_0(X5)) | ~l1_orders_2(X5) | v2_struct_0(X5)).
% 0.22/0.59  
% 0.22/0.59  cnf(u50,axiom,
% 0.22/0.59      ~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u40,negated_conjecture,
% 0.22/0.59      v2_lattice3(sK0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u72,negated_conjecture,
% 0.22/0.59      ~v2_lattice3(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_yellow_0(sK0,k2_tarski(X1,X0))).
% 0.22/0.59  
% 0.22/0.59  cnf(u80,negated_conjecture,
% 0.22/0.59      ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k12_lattice3(sK0,X0,X1) = k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0))).
% 0.22/0.59  
% 0.22/0.59  cnf(u41,negated_conjecture,
% 0.22/0.59      l1_orders_2(sK0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u73,negated_conjecture,
% 0.22/0.59      ~l1_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_yellow_0(sK0,k2_tarski(X0,X1))).
% 0.22/0.59  
% 0.22/0.59  cnf(u81,negated_conjecture,
% 0.22/0.59      ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k12_lattice3(sK0,X0,X1) = k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0))).
% 0.22/0.59  
% 0.22/0.59  cnf(u70,negated_conjecture,
% 0.22/0.59      v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK1) = k2_tarski(sK1,sK1)).
% 0.22/0.59  
% 0.22/0.59  cnf(u64,axiom,
% 0.22/0.59      ~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)).
% 0.22/0.59  
% 0.22/0.59  cnf(u42,negated_conjecture,
% 0.22/0.59      ~v1_xboole_0(sK1)).
% 0.22/0.59  
% 0.22/0.59  cnf(u61,axiom,
% 0.22/0.59      m1_subset_1(sK5(X0),u1_struct_0(X0)) | v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u60,axiom,
% 0.22/0.59      m1_subset_1(sK4(X0),u1_struct_0(X0)) | v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u53,axiom,
% 0.22/0.59      m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | v5_yellow_0(X1,X0) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u52,axiom,
% 0.22/0.59      m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v5_yellow_0(X1,X0) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u44,negated_conjecture,
% 0.22/0.59      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.59  
% 0.22/0.59  cnf(u82,negated_conjecture,
% 0.22/0.59      ~m1_subset_1(X1,u1_struct_0(sK0)) | k12_lattice3(sK0,X0,X1) = k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 0.22/0.59  
% 0.22/0.59  cnf(u71,negated_conjecture,
% 0.22/0.59      ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK1) = k2_tarski(sK1,sK1) | ~r2_hidden(X1,X0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u65,negated_conjecture,
% 0.22/0.59      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k2_tarski(sK1,X0) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.59  
% 0.22/0.59  cnf(u63,axiom,
% 0.22/0.59      ~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) | v1_xboole_0(X0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u55,axiom,
% 0.22/0.59      r2_hidden(sK3(X0,X1),u1_struct_0(X1)) | v5_yellow_0(X1,X0) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u54,axiom,
% 0.22/0.59      r2_hidden(sK2(X0,X1),u1_struct_0(X1)) | v5_yellow_0(X1,X0) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u57,axiom,
% 0.22/0.59      ~r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK2(X0,X1),sK3(X0,X1))),u1_struct_0(X1)) | v5_yellow_0(X1,X0) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.59  
% 0.22/0.59  % (3726)# SZS output end Saturation.
% 0.22/0.59  % (3726)------------------------------
% 0.22/0.59  % (3726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (3726)Termination reason: Satisfiable
% 0.22/0.59  
% 0.22/0.59  % (3726)Memory used [KB]: 1663
% 0.22/0.59  % (3726)Time elapsed: 0.107 s
% 0.22/0.59  % (3726)------------------------------
% 0.22/0.59  % (3726)------------------------------
% 0.22/0.59  % (3716)Success in time 0.219 s
%------------------------------------------------------------------------------

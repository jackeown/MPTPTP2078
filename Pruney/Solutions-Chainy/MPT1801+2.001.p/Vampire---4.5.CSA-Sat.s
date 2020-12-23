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
% DateTime   : Thu Dec  3 13:19:35 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   45 (  45 expanded)
%              Number of leaves         :   45 (  45 expanded)
%              Depth                    :    0
%              Number of atoms          :  155 ( 155 expanded)
%              Number of equality atoms :   26 (  26 expanded)
%              Maximal clause size      :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u119,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0))) )).

cnf(u83,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k3_struct_0(sK0)) )).

cnf(u41,axiom,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | v2_struct_0(X0)
    | k9_tmap_1(X0,X1) = X2 )).

% (25091)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
cnf(u141,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X3)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),sK2(k8_tmap_1(sK0,sK1),X3,X4))),X4,k7_tmap_1(k8_tmap_1(sK0,sK1),sK2(k8_tmap_1(sK0,sK1),X3,X4)))
    | ~ m1_pre_topc(X3,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X3)))))
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | k9_tmap_1(k8_tmap_1(sK0,sK1),X3) = X4 )).

cnf(u131,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK2(sK0,sK1,X0))),X0,k7_tmap_1(sK0,sK2(sK0,sK1,X0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k9_tmap_1(sK0,sK1) = X0 )).

cnf(u88,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) )).

cnf(u65,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(sK0,sK1)) )).

cnf(u31,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) )).

cnf(u59,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) )).

% (25090)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
cnf(u56,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) )).

cnf(u51,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1)) )).

cnf(u50,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_pre_topc(k8_tmap_1(X0,X1)) )).

cnf(u49,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v1_pre_topc(k8_tmap_1(X0,X1)) )).

cnf(u48,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) )).

cnf(u47,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) )).

cnf(u46,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v1_funct_1(k9_tmap_1(X0,X1)) )).

cnf(u45,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )).

cnf(u37,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) )).

cnf(u101,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

cnf(u61,negated_conjecture,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u145,negated_conjecture,
    ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X8)))))
    | ~ m1_pre_topc(X8,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_1(X7)
    | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X8)))
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | u1_struct_0(X8) = sK2(k8_tmap_1(sK0,sK1),X8,X7)
    | k9_tmap_1(k8_tmap_1(sK0,sK1),X8) = X7 )).

cnf(u143,negated_conjecture,
    ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6)))))
    | ~ m1_pre_topc(X6,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6)))
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | m1_subset_1(sK2(k8_tmap_1(sK0,sK1),X6,X5),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_tmap_1(k8_tmap_1(sK0,sK1),X6) = X5 )).

cnf(u139,negated_conjecture,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
    | u1_struct_0(sK1) = sK2(sK0,sK1,X2)
    | k9_tmap_1(sK0,sK1) = X2 )).

cnf(u135,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0))
    | m1_subset_1(sK2(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = X1 )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | v2_struct_0(X0)
    | u1_struct_0(X1) = sK2(X0,X1,X2)
    | k9_tmap_1(X0,X1) = X2 )).

cnf(u39,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | v2_struct_0(X0)
    | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | k9_tmap_1(X0,X1) = X2 )).

cnf(u149,negated_conjecture,
    ( ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),X10) )).

cnf(u147,negated_conjecture,
    ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | k6_tmap_1(k8_tmap_1(sK0,sK1),X9) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(k8_tmap_1(sK0,sK1),X9)) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) )).

cnf(u43,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) )).

cnf(u73,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1)) )).

cnf(u34,negated_conjecture,
    ( v2_pre_topc(sK0) )).

cnf(u150,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1)) )).

cnf(u151,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1))) )).

cnf(u33,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u30,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u69,negated_conjecture,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1)) )).

cnf(u36,axiom,
    ( ~ v1_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 )).

cnf(u77,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1)) )).

cnf(u35,negated_conjecture,
    ( l1_pre_topc(sK0) )).

cnf(u96,negated_conjecture,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))) )).

cnf(u113,negated_conjecture,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) )).

cnf(u118,negated_conjecture,
    ( k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0)) )).

cnf(u93,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) )).

cnf(u82,negated_conjecture,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:28:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (25088)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (25088)Refutation not found, incomplete strategy% (25088)------------------------------
% 0.22/0.48  % (25088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (25088)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (25088)Memory used [KB]: 10746
% 0.22/0.48  % (25088)Time elapsed: 0.012 s
% 0.22/0.48  % (25088)------------------------------
% 0.22/0.48  % (25088)------------------------------
% 0.22/0.49  % (25087)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (25092)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (25095)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (25096)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (25099)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.49  % (25082)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (25083)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (25082)Refutation not found, incomplete strategy% (25082)------------------------------
% 0.22/0.50  % (25082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (25082)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (25082)Memory used [KB]: 6268
% 0.22/0.50  % (25082)Time elapsed: 0.073 s
% 0.22/0.50  % (25082)------------------------------
% 0.22/0.50  % (25082)------------------------------
% 0.22/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.50  % (25099)# SZS output start Saturation.
% 0.22/0.50  cnf(u119,negated_conjecture,
% 0.22/0.50      r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)))).
% 0.22/0.50  
% 0.22/0.50  cnf(u83,negated_conjecture,
% 0.22/0.50      ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k3_struct_0(sK0))).
% 0.22/0.50  
% 0.22/0.50  cnf(u41,axiom,
% 0.22/0.50      ~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | v2_struct_0(X0) | k9_tmap_1(X0,X1) = X2).
% 0.22/0.50  
% 0.22/0.50  % (25091)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  cnf(u141,negated_conjecture,
% 0.22/0.50      ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X3)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),sK2(k8_tmap_1(sK0,sK1),X3,X4))),X4,k7_tmap_1(k8_tmap_1(sK0,sK1),sK2(k8_tmap_1(sK0,sK1),X3,X4))) | ~m1_pre_topc(X3,k8_tmap_1(sK0,sK1)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X3))))) | v2_struct_0(k8_tmap_1(sK0,sK1)) | k9_tmap_1(k8_tmap_1(sK0,sK1),X3) = X4).
% 0.22/0.50  
% 0.22/0.50  cnf(u131,negated_conjecture,
% 0.22/0.50      ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK2(sK0,sK1,X0))),X0,k7_tmap_1(sK0,sK2(sK0,sK1,X0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k9_tmap_1(sK0,sK1) = X0).
% 0.22/0.50  
% 0.22/0.50  cnf(u88,negated_conjecture,
% 0.22/0.50      v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))).
% 0.22/0.50  
% 0.22/0.50  cnf(u65,negated_conjecture,
% 0.22/0.50      v1_funct_1(k9_tmap_1(sK0,sK1))).
% 0.22/0.50  
% 0.22/0.50  cnf(u31,negated_conjecture,
% 0.22/0.50      m1_pre_topc(sK1,sK0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u59,axiom,
% 0.22/0.50      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))).
% 0.22/0.50  
% 0.22/0.50  % (25090)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  cnf(u56,axiom,
% 0.22/0.50      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))).
% 0.22/0.50  
% 0.22/0.50  cnf(u51,axiom,
% 0.22/0.50      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | l1_pre_topc(k8_tmap_1(X0,X1))).
% 0.22/0.50  
% 0.22/0.50  cnf(u50,axiom,
% 0.22/0.50      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_pre_topc(k8_tmap_1(X0,X1))).
% 0.22/0.50  
% 0.22/0.50  cnf(u49,axiom,
% 0.22/0.50      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_pre_topc(k8_tmap_1(X0,X1))).
% 0.22/0.50  
% 0.22/0.50  cnf(u48,axiom,
% 0.22/0.50      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))).
% 0.22/0.50  
% 0.22/0.50  cnf(u47,axiom,
% 0.22/0.50      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))).
% 0.22/0.50  
% 0.22/0.50  cnf(u46,axiom,
% 0.22/0.50      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_1(k9_tmap_1(X0,X1))).
% 0.22/0.50  
% 0.22/0.50  cnf(u45,axiom,
% 0.22/0.50      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))).
% 0.22/0.50  
% 0.22/0.50  cnf(u37,axiom,
% 0.22/0.50      ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))).
% 0.22/0.50  
% 0.22/0.50  cnf(u101,negated_conjecture,
% 0.22/0.50      m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.22/0.50  
% 0.22/0.50  cnf(u61,negated_conjecture,
% 0.22/0.50      m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.50  
% 0.22/0.50  cnf(u145,negated_conjecture,
% 0.22/0.50      ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X8))))) | ~m1_pre_topc(X8,k8_tmap_1(sK0,sK1)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X8))) | v2_struct_0(k8_tmap_1(sK0,sK1)) | u1_struct_0(X8) = sK2(k8_tmap_1(sK0,sK1),X8,X7) | k9_tmap_1(k8_tmap_1(sK0,sK1),X8) = X7).
% 0.22/0.50  
% 0.22/0.50  cnf(u143,negated_conjecture,
% 0.22/0.50      ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6))))) | ~m1_pre_topc(X6,k8_tmap_1(sK0,sK1)) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6))) | v2_struct_0(k8_tmap_1(sK0,sK1)) | m1_subset_1(sK2(k8_tmap_1(sK0,sK1),X6,X5),k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(k8_tmap_1(sK0,sK1),X6) = X5).
% 0.22/0.50  
% 0.22/0.50  cnf(u139,negated_conjecture,
% 0.22/0.50      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0)) | u1_struct_0(sK1) = sK2(sK0,sK1,X2) | k9_tmap_1(sK0,sK1) = X2).
% 0.22/0.50  
% 0.22/0.50  cnf(u135,negated_conjecture,
% 0.22/0.50      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0)) | m1_subset_1(sK2(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = X1).
% 0.22/0.50  
% 0.22/0.50  cnf(u40,axiom,
% 0.22/0.50      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | v2_struct_0(X0) | u1_struct_0(X1) = sK2(X0,X1,X2) | k9_tmap_1(X0,X1) = X2).
% 0.22/0.50  
% 0.22/0.50  cnf(u39,axiom,
% 0.22/0.50      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | v2_struct_0(X0) | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) = X2).
% 0.22/0.50  
% 0.22/0.50  cnf(u149,negated_conjecture,
% 0.22/0.50      ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k8_tmap_1(sK0,sK1)) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),X10)).
% 0.22/0.50  
% 0.22/0.50  cnf(u147,negated_conjecture,
% 0.22/0.50      ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k8_tmap_1(sK0,sK1)) | k6_tmap_1(k8_tmap_1(sK0,sK1),X9) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(k8_tmap_1(sK0,sK1),X9))).
% 0.22/0.50  
% 0.22/0.50  cnf(u42,axiom,
% 0.22/0.50      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))).
% 0.22/0.50  
% 0.22/0.50  cnf(u43,axiom,
% 0.22/0.50      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))).
% 0.22/0.50  
% 0.22/0.50  cnf(u73,negated_conjecture,
% 0.22/0.50      v2_pre_topc(k8_tmap_1(sK0,sK1))).
% 0.22/0.50  
% 0.22/0.50  cnf(u34,negated_conjecture,
% 0.22/0.50      v2_pre_topc(sK0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u150,negated_conjecture,
% 0.22/0.50      v2_struct_0(k8_tmap_1(sK0,sK1)) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1))).
% 0.22/0.50  
% 0.22/0.50  cnf(u151,negated_conjecture,
% 0.22/0.50      v2_struct_0(k8_tmap_1(sK0,sK1)) | k6_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1)))).
% 0.22/0.50  
% 0.22/0.50  cnf(u33,negated_conjecture,
% 0.22/0.50      ~v2_struct_0(sK0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u30,negated_conjecture,
% 0.22/0.50      ~v2_struct_0(sK1)).
% 0.22/0.50  
% 0.22/0.50  cnf(u69,negated_conjecture,
% 0.22/0.50      v1_pre_topc(k8_tmap_1(sK0,sK1))).
% 0.22/0.50  
% 0.22/0.50  cnf(u36,axiom,
% 0.22/0.50      ~v1_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0).
% 0.22/0.50  
% 0.22/0.50  cnf(u77,negated_conjecture,
% 0.22/0.50      l1_pre_topc(k8_tmap_1(sK0,sK1))).
% 0.22/0.50  
% 0.22/0.50  cnf(u35,negated_conjecture,
% 0.22/0.50      l1_pre_topc(sK0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u96,negated_conjecture,
% 0.22/0.50      k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1)))).
% 0.22/0.50  
% 0.22/0.50  cnf(u113,negated_conjecture,
% 0.22/0.50      k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))).
% 0.22/0.50  
% 0.22/0.50  cnf(u118,negated_conjecture,
% 0.22/0.50      k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0))).
% 0.22/0.50  
% 0.22/0.50  cnf(u93,negated_conjecture,
% 0.22/0.50      u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))).
% 0.22/0.50  
% 0.22/0.50  cnf(u82,negated_conjecture,
% 0.22/0.50      u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))).
% 0.22/0.50  
% 0.22/0.50  % (25099)# SZS output end Saturation.
% 0.22/0.50  % (25099)------------------------------
% 0.22/0.50  % (25099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (25099)Termination reason: Satisfiable
% 0.22/0.50  
% 0.22/0.50  % (25099)Memory used [KB]: 1791
% 0.22/0.50  % (25099)Time elapsed: 0.080 s
% 0.22/0.50  % (25099)------------------------------
% 0.22/0.50  % (25099)------------------------------
% 0.22/0.50  % (25080)Success in time 0.138 s
%------------------------------------------------------------------------------

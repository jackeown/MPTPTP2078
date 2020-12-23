%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:35 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   47 (  47 expanded)
%              Number of leaves         :   47 (  47 expanded)
%              Depth                    :    0
%              Number of atoms          :  188 ( 188 expanded)
%              Number of equality atoms :   32 (  32 expanded)
%              Maximal clause size      :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u130,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0))) )).

cnf(u92,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k3_struct_0(sK0)) )).

cnf(u41,axiom,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK3(X0,X1,X2))),X2,k7_tmap_1(X0,sK3(X0,X1,X2)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | v2_struct_0(X0)
    | k9_tmap_1(X0,X1) = X2 )).

cnf(u151,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X3)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),sK3(k8_tmap_1(sK0,sK1),X3,X4))),X4,k7_tmap_1(k8_tmap_1(sK0,sK1),sK3(k8_tmap_1(sK0,sK1),X3,X4)))
    | ~ m1_pre_topc(X3,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X3)))))
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | k9_tmap_1(k8_tmap_1(sK0,sK1),X3) = X4 )).

cnf(u141,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK3(sK0,sK1,X0))),X0,k7_tmap_1(sK0,sK3(sK0,sK1,X0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k9_tmap_1(sK0,sK1) = X0 )).

cnf(u97,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) )).

cnf(u70,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(sK0,sK1)) )).

cnf(u74,negated_conjecture,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1)) )).

cnf(u111,negated_conjecture,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(sK1) = sK2(sK0,sK1,X0)
    | k8_tmap_1(sK0,sK1) = X0 )).

cnf(u115,negated_conjecture,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | m1_subset_1(sK2(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = X0 )).

cnf(u119,negated_conjecture,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(sK0,sK2(sK0,sK1,X0)) != X0
    | k8_tmap_1(sK0,sK1) = X0 )).

cnf(u28,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) )).

cnf(u64,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) )).

cnf(u61,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) )).

cnf(u58,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) )).

cnf(u50,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1)) )).

cnf(u49,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_pre_topc(k8_tmap_1(X0,X1)) )).

cnf(u48,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v1_pre_topc(k8_tmap_1(X0,X1)) )).

cnf(u47,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) )).

cnf(u46,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) )).

cnf(u45,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v1_funct_1(k9_tmap_1(X0,X1)) )).

cnf(u44,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )).

cnf(u37,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | k6_tmap_1(X0,sK2(X0,X1,X2)) != X2
    | k8_tmap_1(X0,X1) = X2 )).

cnf(u36,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) = sK2(X0,X1,X2)
    | k8_tmap_1(X0,X1) = X2 )).

cnf(u35,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | k8_tmap_1(X0,X1) = X2 )).

cnf(u33,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) )).

cnf(u107,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

cnf(u66,negated_conjecture,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u155,negated_conjecture,
    ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X8)))))
    | ~ m1_pre_topc(X8,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_1(X7)
    | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X8)))
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | u1_struct_0(X8) = sK3(k8_tmap_1(sK0,sK1),X8,X7)
    | k9_tmap_1(k8_tmap_1(sK0,sK1),X8) = X7 )).

cnf(u153,negated_conjecture,
    ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6)))))
    | ~ m1_pre_topc(X6,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6)))
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | m1_subset_1(sK3(k8_tmap_1(sK0,sK1),X6,X5),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_tmap_1(k8_tmap_1(sK0,sK1),X6) = X5 )).

cnf(u149,negated_conjecture,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
    | u1_struct_0(sK1) = sK3(sK0,sK1,X2)
    | k9_tmap_1(sK0,sK1) = X2 )).

cnf(u145,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = X1 )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | v2_struct_0(X0)
    | u1_struct_0(X1) = sK3(X0,X1,X2)
    | k9_tmap_1(X0,X1) = X2 )).

cnf(u39,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | v2_struct_0(X0)
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | k9_tmap_1(X0,X1) = X2 )).

cnf(u157,negated_conjecture,
    ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k8_tmap_1(sK0,sK1))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),X9) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) )).

cnf(u78,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1)) )).

cnf(u31,negated_conjecture,
    ( v2_pre_topc(sK0) )).

cnf(u161,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1)) )).

cnf(u30,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u27,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u82,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1)) )).

cnf(u32,negated_conjecture,
    ( l1_pre_topc(sK0) )).

cnf(u102,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) )).

cnf(u86,negated_conjecture,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) )).

cnf(u129,negated_conjecture,
    ( k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0)) )).

cnf(u91,negated_conjecture,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (24802)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (24794)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.51  % (24800)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (24787)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (24801)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.51  % (24796)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (24792)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (24788)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (24793)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.52  % (24788)Refutation not found, incomplete strategy% (24788)------------------------------
% 0.20/0.52  % (24788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24788)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24788)Memory used [KB]: 10618
% 0.20/0.52  % (24788)Time elapsed: 0.107 s
% 0.20/0.52  % (24788)------------------------------
% 0.20/0.52  % (24788)------------------------------
% 0.20/0.52  % (24800)Refutation not found, incomplete strategy% (24800)------------------------------
% 0.20/0.52  % (24800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24804)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.53  % (24803)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.53  % (24796)Refutation not found, incomplete strategy% (24796)------------------------------
% 0.20/0.53  % (24796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24787)Refutation not found, incomplete strategy% (24787)------------------------------
% 0.20/0.53  % (24787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24787)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (24787)Memory used [KB]: 6268
% 0.20/0.53  % (24787)Time elapsed: 0.101 s
% 0.20/0.53  % (24787)------------------------------
% 0.20/0.53  % (24787)------------------------------
% 0.20/0.53  % (24795)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.53  % (24804)# SZS output start Saturation.
% 0.20/0.53  cnf(u130,negated_conjecture,
% 0.20/0.53      r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)))).
% 0.20/0.53  
% 0.20/0.53  cnf(u92,negated_conjecture,
% 0.20/0.53      ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k3_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u41,axiom,
% 0.20/0.53      ~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK3(X0,X1,X2))),X2,k7_tmap_1(X0,sK3(X0,X1,X2))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | v2_struct_0(X0) | k9_tmap_1(X0,X1) = X2).
% 0.20/0.53  
% 0.20/0.53  cnf(u151,negated_conjecture,
% 0.20/0.53      ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X3)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(k8_tmap_1(sK0,sK1),sK3(k8_tmap_1(sK0,sK1),X3,X4))),X4,k7_tmap_1(k8_tmap_1(sK0,sK1),sK3(k8_tmap_1(sK0,sK1),X3,X4))) | ~m1_pre_topc(X3,k8_tmap_1(sK0,sK1)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X3))))) | v2_struct_0(k8_tmap_1(sK0,sK1)) | k9_tmap_1(k8_tmap_1(sK0,sK1),X3) = X4).
% 0.20/0.53  
% 0.20/0.53  cnf(u141,negated_conjecture,
% 0.20/0.53      ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK3(sK0,sK1,X0))),X0,k7_tmap_1(sK0,sK3(sK0,sK1,X0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k9_tmap_1(sK0,sK1) = X0).
% 0.20/0.53  
% 0.20/0.53  cnf(u97,negated_conjecture,
% 0.20/0.53      v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u70,negated_conjecture,
% 0.20/0.53      v1_funct_1(k9_tmap_1(sK0,sK1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u74,negated_conjecture,
% 0.20/0.53      v1_pre_topc(k8_tmap_1(sK0,sK1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u111,negated_conjecture,
% 0.20/0.53      ~v1_pre_topc(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | u1_struct_0(sK1) = sK2(sK0,sK1,X0) | k8_tmap_1(sK0,sK1) = X0).
% 0.20/0.53  
% 0.20/0.53  cnf(u115,negated_conjecture,
% 0.20/0.53      ~v1_pre_topc(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | m1_subset_1(sK2(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = X0).
% 0.20/0.53  
% 0.20/0.53  cnf(u119,negated_conjecture,
% 0.20/0.53      ~v1_pre_topc(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k6_tmap_1(sK0,sK2(sK0,sK1,X0)) != X0 | k8_tmap_1(sK0,sK1) = X0).
% 0.20/0.53  
% 0.20/0.53  cnf(u28,negated_conjecture,
% 0.20/0.53      m1_pre_topc(sK1,sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u64,axiom,
% 0.20/0.53      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u61,axiom,
% 0.20/0.53      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))).
% 0.20/0.53  
% 0.20/0.53  cnf(u58,axiom,
% 0.20/0.53      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u50,axiom,
% 0.20/0.53      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | l1_pre_topc(k8_tmap_1(X0,X1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u49,axiom,
% 0.20/0.53      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_pre_topc(k8_tmap_1(X0,X1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u48,axiom,
% 0.20/0.53      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_pre_topc(k8_tmap_1(X0,X1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u47,axiom,
% 0.20/0.53      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))).
% 0.20/0.53  
% 0.20/0.53  cnf(u46,axiom,
% 0.20/0.53      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))).
% 0.20/0.53  
% 0.20/0.53  cnf(u45,axiom,
% 0.20/0.53      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_1(k9_tmap_1(X0,X1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u44,axiom,
% 0.20/0.53      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u37,axiom,
% 0.20/0.53      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | k6_tmap_1(X0,sK2(X0,X1,X2)) != X2 | k8_tmap_1(X0,X1) = X2).
% 0.20/0.53  
% 0.20/0.53  cnf(u36,axiom,
% 0.20/0.53      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | u1_struct_0(X1) = sK2(X0,X1,X2) | k8_tmap_1(X0,X1) = X2).
% 0.20/0.53  
% 0.20/0.53  cnf(u35,axiom,
% 0.20/0.53      ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) = X2).
% 0.20/0.53  
% 0.20/0.53  cnf(u33,axiom,
% 0.20/0.53      ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))).
% 0.20/0.53  
% 0.20/0.53  cnf(u107,negated_conjecture,
% 0.20/0.53      m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.20/0.53  
% 0.20/0.53  cnf(u66,negated_conjecture,
% 0.20/0.53      m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.53  
% 0.20/0.53  cnf(u155,negated_conjecture,
% 0.20/0.53      ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X8))))) | ~m1_pre_topc(X8,k8_tmap_1(sK0,sK1)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X8))) | v2_struct_0(k8_tmap_1(sK0,sK1)) | u1_struct_0(X8) = sK3(k8_tmap_1(sK0,sK1),X8,X7) | k9_tmap_1(k8_tmap_1(sK0,sK1),X8) = X7).
% 0.20/0.53  
% 0.20/0.53  cnf(u153,negated_conjecture,
% 0.20/0.53      ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6))))) | ~m1_pre_topc(X6,k8_tmap_1(sK0,sK1)) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(k8_tmap_1(sK0,sK1),X6))) | v2_struct_0(k8_tmap_1(sK0,sK1)) | m1_subset_1(sK3(k8_tmap_1(sK0,sK1),X6,X5),k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(k8_tmap_1(sK0,sK1),X6) = X5).
% 0.20/0.53  
% 0.20/0.53  cnf(u149,negated_conjecture,
% 0.20/0.53      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0)) | u1_struct_0(sK1) = sK3(sK0,sK1,X2) | k9_tmap_1(sK0,sK1) = X2).
% 0.20/0.53  
% 0.20/0.53  cnf(u145,negated_conjecture,
% 0.20/0.53      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = X1).
% 0.20/0.53  
% 0.20/0.53  cnf(u40,axiom,
% 0.20/0.53      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | v2_struct_0(X0) | u1_struct_0(X1) = sK3(X0,X1,X2) | k9_tmap_1(X0,X1) = X2).
% 0.20/0.53  
% 0.20/0.53  cnf(u39,axiom,
% 0.20/0.53      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | v2_struct_0(X0) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) = X2).
% 0.20/0.53  
% 0.20/0.53  cnf(u157,negated_conjecture,
% 0.20/0.53      ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k8_tmap_1(sK0,sK1)) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),X9)).
% 0.20/0.53  
% 0.20/0.53  cnf(u42,axiom,
% 0.20/0.53      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u78,negated_conjecture,
% 0.20/0.53      v2_pre_topc(k8_tmap_1(sK0,sK1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u31,negated_conjecture,
% 0.20/0.53      v2_pre_topc(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u161,negated_conjecture,
% 0.20/0.53      v2_struct_0(k8_tmap_1(sK0,sK1)) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(k8_tmap_1(sK0,sK1),u1_struct_0(sK1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u30,negated_conjecture,
% 0.20/0.53      ~v2_struct_0(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u27,negated_conjecture,
% 0.20/0.53      ~v2_struct_0(sK1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u82,negated_conjecture,
% 0.20/0.53      l1_pre_topc(k8_tmap_1(sK0,sK1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u32,negated_conjecture,
% 0.20/0.53      l1_pre_topc(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u102,negated_conjecture,
% 0.20/0.53      u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u86,negated_conjecture,
% 0.20/0.53      k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u129,negated_conjecture,
% 0.20/0.53      k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u91,negated_conjecture,
% 0.20/0.53      u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))).
% 0.20/0.53  
% 0.20/0.53  % (24804)# SZS output end Saturation.
% 0.20/0.53  % (24804)------------------------------
% 0.20/0.53  % (24804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24804)Termination reason: Satisfiable
% 0.20/0.53  
% 0.20/0.53  % (24804)Memory used [KB]: 1791
% 0.20/0.53  % (24804)Time elapsed: 0.125 s
% 0.20/0.53  % (24804)------------------------------
% 0.20/0.53  % (24804)------------------------------
% 0.20/0.53  % (24786)Success in time 0.178 s
%------------------------------------------------------------------------------

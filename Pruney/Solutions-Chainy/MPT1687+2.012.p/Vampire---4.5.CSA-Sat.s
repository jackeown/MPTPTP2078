%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:21 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   25 (  25 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    0
%              Number of atoms          :   46 (  46 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u32,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u30,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u34,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u45,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u44,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u31,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u29,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u62,negated_conjecture,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

cnf(u65,negated_conjecture,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK1) )).

cnf(u73,negated_conjecture,
    ( v1_partfun1(sK2,k1_relat_1(sK2)) )).

cnf(u37,axiom,
    ( ~ v1_partfun1(X1,X0)
    | ~ v4_relat_1(X1,X0)
    | k1_relat_1(X1) = X0
    | ~ v1_relat_1(X1) )).

cnf(u64,negated_conjecture,
    ( v4_relat_1(sK2,k1_relat_1(sK2)) )).

cnf(u42,axiom,
    ( ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | v1_partfun1(X1,k1_relat_1(X1)) )).

cnf(u63,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u68,negated_conjecture,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

cnf(u43,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ v1_funct_1(X2)
    | v1_partfun1(X2,k1_xboole_0) )).

cnf(u38,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(X2) )).

cnf(u39,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v4_relat_1(X2,X0) )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_1(X2)
    | k1_xboole_0 = X1
    | v1_partfun1(X2,X0) )).

cnf(u26,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u46,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u33,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u78,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(sK2)) )).

cnf(u35,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u60,negated_conjecture,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:33:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (3091)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.47  % (3091)Refutation not found, incomplete strategy% (3091)------------------------------
% 0.22/0.47  % (3091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (3091)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (3091)Memory used [KB]: 1663
% 0.22/0.47  % (3091)Time elapsed: 0.011 s
% 0.22/0.47  % (3091)------------------------------
% 0.22/0.47  % (3091)------------------------------
% 0.22/0.47  % (3102)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (3094)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (3092)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (3089)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (3087)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (3104)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (3093)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (3087)Refutation not found, incomplete strategy% (3087)------------------------------
% 0.22/0.50  % (3087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (3087)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (3087)Memory used [KB]: 6140
% 0.22/0.50  % (3087)Time elapsed: 0.088 s
% 0.22/0.50  % (3087)------------------------------
% 0.22/0.50  % (3087)------------------------------
% 0.22/0.50  % (3095)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (3088)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (3090)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (3088)Refutation not found, incomplete strategy% (3088)------------------------------
% 0.22/0.50  % (3088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (3088)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (3088)Memory used [KB]: 10618
% 0.22/0.50  % (3088)Time elapsed: 0.093 s
% 0.22/0.50  % (3088)------------------------------
% 0.22/0.50  % (3088)------------------------------
% 0.22/0.50  % (3090)Refutation not found, incomplete strategy% (3090)------------------------------
% 0.22/0.50  % (3090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (3090)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (3090)Memory used [KB]: 10746
% 0.22/0.50  % (3090)Time elapsed: 0.094 s
% 0.22/0.50  % (3090)------------------------------
% 0.22/0.50  % (3090)------------------------------
% 0.22/0.51  % (3108)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (3107)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (3108)Refutation not found, incomplete strategy% (3108)------------------------------
% 0.22/0.51  % (3108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3108)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3108)Memory used [KB]: 10618
% 0.22/0.51  % (3108)Time elapsed: 0.105 s
% 0.22/0.51  % (3108)------------------------------
% 0.22/0.51  % (3108)------------------------------
% 0.22/0.51  % (3103)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (3089)Refutation not found, incomplete strategy% (3089)------------------------------
% 0.22/0.51  % (3089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3089)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3089)Memory used [KB]: 10618
% 0.22/0.51  % (3089)Time elapsed: 0.086 s
% 0.22/0.51  % (3089)------------------------------
% 0.22/0.51  % (3089)------------------------------
% 0.22/0.51  % (3101)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (3103)Refutation not found, incomplete strategy% (3103)------------------------------
% 0.22/0.51  % (3103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3103)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3103)Memory used [KB]: 6140
% 0.22/0.51  % (3103)Time elapsed: 0.105 s
% 0.22/0.51  % (3103)------------------------------
% 0.22/0.51  % (3103)------------------------------
% 0.22/0.51  % (3107)Refutation not found, incomplete strategy% (3107)------------------------------
% 0.22/0.51  % (3107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3107)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3107)Memory used [KB]: 6140
% 0.22/0.51  % (3107)Time elapsed: 0.107 s
% 0.22/0.51  % (3107)------------------------------
% 0.22/0.51  % (3107)------------------------------
% 0.22/0.51  % (3106)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (3101)Refutation not found, incomplete strategy% (3101)------------------------------
% 0.22/0.51  % (3101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3101)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3101)Memory used [KB]: 1663
% 0.22/0.51  % (3101)Time elapsed: 0.105 s
% 0.22/0.51  % (3101)------------------------------
% 0.22/0.51  % (3101)------------------------------
% 0.22/0.51  % (3099)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (3093)Refutation not found, incomplete strategy% (3093)------------------------------
% 0.22/0.52  % (3093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3093)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (3093)Memory used [KB]: 10618
% 0.22/0.52  % (3093)Time elapsed: 0.103 s
% 0.22/0.52  % (3093)------------------------------
% 0.22/0.52  % (3093)------------------------------
% 0.22/0.52  % (3106)Refutation not found, incomplete strategy% (3106)------------------------------
% 0.22/0.52  % (3106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3106)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (3106)Memory used [KB]: 1663
% 0.22/0.52  % (3106)Time elapsed: 0.109 s
% 0.22/0.52  % (3106)------------------------------
% 0.22/0.52  % (3106)------------------------------
% 0.22/0.52  % (3099)Refutation not found, incomplete strategy% (3099)------------------------------
% 0.22/0.52  % (3099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3099)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (3099)Memory used [KB]: 10618
% 0.22/0.52  % (3099)Time elapsed: 0.107 s
% 0.22/0.52  % (3099)------------------------------
% 0.22/0.52  % (3099)------------------------------
% 0.22/0.52  % (3097)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (3098)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (3100)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (3105)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % (3100)Refutation not found, incomplete strategy% (3100)------------------------------
% 0.22/0.52  % (3100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3100)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (3100)Memory used [KB]: 6012
% 0.22/0.52  % (3100)Time elapsed: 0.003 s
% 0.22/0.52  % (3100)------------------------------
% 0.22/0.52  % (3100)------------------------------
% 0.22/0.52  % (3098)Refutation not found, incomplete strategy% (3098)------------------------------
% 0.22/0.52  % (3098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3098)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (3098)Memory used [KB]: 6140
% 0.22/0.52  % (3098)Time elapsed: 0.108 s
% 0.22/0.52  % (3098)------------------------------
% 0.22/0.52  % (3098)------------------------------
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (3105)# SZS output start Saturation.
% 0.22/0.52  cnf(u32,negated_conjecture,
% 0.22/0.52      l1_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u30,negated_conjecture,
% 0.22/0.52      l1_orders_2(sK1)).
% 0.22/0.52  
% 0.22/0.52  cnf(u34,axiom,
% 0.22/0.52      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u45,negated_conjecture,
% 0.22/0.52      l1_struct_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u44,negated_conjecture,
% 0.22/0.52      l1_struct_0(sK1)).
% 0.22/0.52  
% 0.22/0.52  cnf(u31,negated_conjecture,
% 0.22/0.52      ~v2_struct_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u29,negated_conjecture,
% 0.22/0.52      ~v2_struct_0(sK1)).
% 0.22/0.52  
% 0.22/0.52  cnf(u62,negated_conjecture,
% 0.22/0.52      v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))).
% 0.22/0.52  
% 0.22/0.52  cnf(u65,negated_conjecture,
% 0.22/0.52      v1_partfun1(sK2,k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK1)).
% 0.22/0.52  
% 0.22/0.52  cnf(u73,negated_conjecture,
% 0.22/0.52      v1_partfun1(sK2,k1_relat_1(sK2))).
% 0.22/0.52  
% 0.22/0.52  cnf(u37,axiom,
% 0.22/0.52      ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)).
% 0.22/0.52  
% 0.22/0.52  cnf(u64,negated_conjecture,
% 0.22/0.52      v4_relat_1(sK2,k1_relat_1(sK2))).
% 0.22/0.52  
% 0.22/0.52  cnf(u42,axiom,
% 0.22/0.52      ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1) | v1_partfun1(X1,k1_relat_1(X1))).
% 0.22/0.52  
% 0.22/0.52  cnf(u63,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 0.22/0.52  
% 0.22/0.52  cnf(u68,negated_conjecture,
% 0.22/0.52      ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))).
% 0.22/0.52  
% 0.22/0.52  cnf(u43,axiom,
% 0.22/0.52      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,k1_xboole_0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u38,axiom,
% 0.22/0.52      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)).
% 0.22/0.52  
% 0.22/0.52  cnf(u39,axiom,
% 0.22/0.52      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u40,axiom,
% 0.22/0.52      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k1_xboole_0 = X1 | v1_partfun1(X2,X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u26,negated_conjecture,
% 0.22/0.52      v1_funct_1(sK2)).
% 0.22/0.52  
% 0.22/0.52  cnf(u46,negated_conjecture,
% 0.22/0.52      v1_relat_1(sK2)).
% 0.22/0.52  
% 0.22/0.52  cnf(u33,axiom,
% 0.22/0.52      v1_xboole_0(k1_xboole_0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u78,negated_conjecture,
% 0.22/0.52      ~v1_xboole_0(k1_relat_1(sK2))).
% 0.22/0.52  
% 0.22/0.52  cnf(u35,axiom,
% 0.22/0.52      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u60,negated_conjecture,
% 0.22/0.52      u1_struct_0(sK0) = k1_relat_1(sK2)).
% 0.22/0.52  
% 0.22/0.52  % (3105)# SZS output end Saturation.
% 0.22/0.52  % (3105)------------------------------
% 0.22/0.52  % (3105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3105)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (3105)Memory used [KB]: 1663
% 0.22/0.52  % (3105)Time elapsed: 0.116 s
% 0.22/0.52  % (3105)------------------------------
% 0.22/0.52  % (3105)------------------------------
% 0.22/0.52  % (3097)Refutation not found, incomplete strategy% (3097)------------------------------
% 0.22/0.52  % (3097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3097)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (3097)Memory used [KB]: 10618
% 0.22/0.52  % (3097)Time elapsed: 0.110 s
% 0.22/0.52  % (3097)------------------------------
% 0.22/0.52  % (3097)------------------------------
% 0.22/0.52  % (3086)Success in time 0.16 s
%------------------------------------------------------------------------------

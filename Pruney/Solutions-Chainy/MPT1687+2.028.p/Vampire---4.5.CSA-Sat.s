%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:23 EST 2020

% Result     : CounterSatisfiable 0.23s
% Output     : Saturation 0.23s
% Verified   : 
% Statistics : Number of clauses        :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   48 (  48 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u33,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u31,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u35,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u47,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u46,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u32,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u30,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u65,negated_conjecture,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

cnf(u76,negated_conjecture,
    ( v1_partfun1(sK2,k1_relat_1(sK2)) )).

cnf(u68,negated_conjecture,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK1) )).

cnf(u40,axiom,
    ( ~ v1_partfun1(X1,X0)
    | ~ v4_relat_1(X1,X0)
    | k1_relat_1(X1) = X0
    | ~ v1_relat_1(X1) )).

cnf(u67,negated_conjecture,
    ( v4_relat_1(sK2,k1_relat_1(sK2)) )).

cnf(u44,axiom,
    ( ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | v1_partfun1(X1,k1_relat_1(X1)) )).

cnf(u27,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u66,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u71,negated_conjecture,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

cnf(u45,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ v1_funct_1(X2)
    | v1_partfun1(X2,k1_xboole_0) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v4_relat_1(X2,X0) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_1(X2)
    | k1_xboole_0 = X1
    | v1_partfun1(X2,X0) )).

cnf(u36,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(X1) )).

cnf(u49,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u38,axiom,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) )).

cnf(u34,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u81,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(sK2)) )).

cnf(u37,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u63,negated_conjecture,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:17:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.50  % (29037)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.50  % (29047)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.23/0.51  % (29040)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.23/0.51  % (29047)Refutation not found, incomplete strategy% (29047)------------------------------
% 0.23/0.51  % (29047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (29047)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.51  
% 0.23/0.51  % (29047)Memory used [KB]: 6140
% 0.23/0.51  % (29047)Time elapsed: 0.008 s
% 0.23/0.51  % (29047)------------------------------
% 0.23/0.51  % (29047)------------------------------
% 0.23/0.51  % (29039)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.23/0.51  % (29032)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.23/0.52  % (29032)Refutation not found, incomplete strategy% (29032)------------------------------
% 0.23/0.52  % (29032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (29032)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (29032)Memory used [KB]: 6140
% 0.23/0.52  % (29032)Time elapsed: 0.075 s
% 0.23/0.52  % (29032)------------------------------
% 0.23/0.52  % (29032)------------------------------
% 0.23/0.52  % (29045)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.23/0.52  % (29045)Refutation not found, incomplete strategy% (29045)------------------------------
% 0.23/0.52  % (29045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (29045)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (29045)Memory used [KB]: 1663
% 0.23/0.52  % (29045)Time elapsed: 0.089 s
% 0.23/0.52  % (29045)------------------------------
% 0.23/0.52  % (29045)------------------------------
% 0.23/0.52  % (29038)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.23/0.53  % (29038)Refutation not found, incomplete strategy% (29038)------------------------------
% 0.23/0.53  % (29038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (29038)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (29038)Memory used [KB]: 10618
% 0.23/0.53  % (29038)Time elapsed: 0.102 s
% 0.23/0.53  % (29038)------------------------------
% 0.23/0.53  % (29038)------------------------------
% 0.23/0.53  % (29034)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.23/0.53  % (29042)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.23/0.54  % (29036)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.23/0.54  % (29033)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.54  % (29033)Refutation not found, incomplete strategy% (29033)------------------------------
% 0.23/0.54  % (29033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (29033)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (29033)Memory used [KB]: 10618
% 0.23/0.54  % (29033)Time elapsed: 0.111 s
% 0.23/0.54  % (29033)------------------------------
% 0.23/0.54  % (29033)------------------------------
% 0.23/0.55  % (29046)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.23/0.55  % (29051)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.23/0.55  % (29052)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.23/0.55  % (29034)Refutation not found, incomplete strategy% (29034)------------------------------
% 0.23/0.55  % (29034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (29034)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (29034)Memory used [KB]: 10618
% 0.23/0.55  % (29034)Time elapsed: 0.097 s
% 0.23/0.55  % (29034)------------------------------
% 0.23/0.55  % (29034)------------------------------
% 0.23/0.55  % (29042)Refutation not found, incomplete strategy% (29042)------------------------------
% 0.23/0.55  % (29042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (29042)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (29042)Memory used [KB]: 6140
% 0.23/0.55  % (29042)Time elapsed: 0.125 s
% 0.23/0.55  % (29042)------------------------------
% 0.23/0.55  % (29042)------------------------------
% 0.23/0.55  % (29036)Refutation not found, incomplete strategy% (29036)------------------------------
% 0.23/0.55  % (29036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (29036)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (29036)Memory used [KB]: 1663
% 0.23/0.55  % (29036)Time elapsed: 0.115 s
% 0.23/0.55  % (29036)------------------------------
% 0.23/0.55  % (29036)------------------------------
% 0.23/0.56  % (29051)Refutation not found, incomplete strategy% (29051)------------------------------
% 0.23/0.56  % (29051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (29051)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (29051)Memory used [KB]: 6140
% 0.23/0.56  % (29051)Time elapsed: 0.124 s
% 0.23/0.56  % (29051)------------------------------
% 0.23/0.56  % (29051)------------------------------
% 0.23/0.56  % (29043)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.23/0.56  % (29052)Refutation not found, incomplete strategy% (29052)------------------------------
% 0.23/0.56  % (29052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (29052)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (29052)Memory used [KB]: 10618
% 0.23/0.56  % (29052)Time elapsed: 0.128 s
% 0.23/0.56  % (29052)------------------------------
% 0.23/0.56  % (29052)------------------------------
% 0.23/0.56  % (29035)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.56  % (29043)Refutation not found, incomplete strategy% (29043)------------------------------
% 0.23/0.56  % (29043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (29043)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (29043)Memory used [KB]: 10618
% 0.23/0.56  % (29043)Time elapsed: 0.127 s
% 0.23/0.56  % (29043)------------------------------
% 0.23/0.56  % (29043)------------------------------
% 0.23/0.56  % (29041)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.23/0.56  % (29035)Refutation not found, incomplete strategy% (29035)------------------------------
% 0.23/0.56  % (29035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (29035)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (29035)Memory used [KB]: 10746
% 0.23/0.56  % (29035)Time elapsed: 0.129 s
% 0.23/0.56  % (29035)------------------------------
% 0.23/0.56  % (29035)------------------------------
% 0.23/0.56  % (29048)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.23/0.56  % (29049)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.23/0.57  % (29041)Refutation not found, incomplete strategy% (29041)------------------------------
% 0.23/0.57  % (29041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (29041)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (29041)Memory used [KB]: 10746
% 0.23/0.57  % (29041)Time elapsed: 0.134 s
% 0.23/0.57  % (29041)------------------------------
% 0.23/0.57  % (29041)------------------------------
% 0.23/0.57  % SZS status CounterSatisfiable for theBenchmark
% 0.23/0.57  % (29049)# SZS output start Saturation.
% 0.23/0.57  cnf(u33,negated_conjecture,
% 0.23/0.57      l1_orders_2(sK0)).
% 0.23/0.57  
% 0.23/0.57  cnf(u31,negated_conjecture,
% 0.23/0.57      l1_orders_2(sK1)).
% 0.23/0.57  
% 0.23/0.57  cnf(u35,axiom,
% 0.23/0.57      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.23/0.57  
% 0.23/0.57  cnf(u47,negated_conjecture,
% 0.23/0.57      l1_struct_0(sK0)).
% 0.23/0.57  
% 0.23/0.57  cnf(u46,negated_conjecture,
% 0.23/0.57      l1_struct_0(sK1)).
% 0.23/0.57  
% 0.23/0.57  cnf(u32,negated_conjecture,
% 0.23/0.57      ~v2_struct_0(sK0)).
% 0.23/0.57  
% 0.23/0.57  cnf(u30,negated_conjecture,
% 0.23/0.57      ~v2_struct_0(sK1)).
% 0.23/0.57  
% 0.23/0.57  cnf(u65,negated_conjecture,
% 0.23/0.57      v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))).
% 0.23/0.57  
% 0.23/0.57  cnf(u76,negated_conjecture,
% 0.23/0.57      v1_partfun1(sK2,k1_relat_1(sK2))).
% 0.23/0.57  
% 0.23/0.57  cnf(u68,negated_conjecture,
% 0.23/0.57      v1_partfun1(sK2,k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK1)).
% 0.23/0.57  
% 0.23/0.57  cnf(u40,axiom,
% 0.23/0.57      ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)).
% 0.23/0.57  
% 0.23/0.57  cnf(u67,negated_conjecture,
% 0.23/0.57      v4_relat_1(sK2,k1_relat_1(sK2))).
% 0.23/0.57  
% 0.23/0.57  cnf(u44,axiom,
% 0.23/0.57      ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1) | v1_partfun1(X1,k1_relat_1(X1))).
% 0.23/0.57  
% 0.23/0.57  cnf(u27,negated_conjecture,
% 0.23/0.57      v1_funct_1(sK2)).
% 0.23/0.57  
% 0.23/0.57  cnf(u66,negated_conjecture,
% 0.23/0.57      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 0.23/0.57  
% 0.23/0.57  cnf(u71,negated_conjecture,
% 0.23/0.57      ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))).
% 0.23/0.57  
% 0.23/0.57  cnf(u45,axiom,
% 0.23/0.57      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,k1_xboole_0)).
% 0.23/0.57  
% 0.23/0.57  cnf(u41,axiom,
% 0.23/0.57      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)).
% 0.23/0.57  
% 0.23/0.57  cnf(u42,axiom,
% 0.23/0.57      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k1_xboole_0 = X1 | v1_partfun1(X2,X0)).
% 0.23/0.57  
% 0.23/0.57  cnf(u36,axiom,
% 0.23/0.57      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)).
% 0.23/0.57  
% 0.23/0.57  cnf(u49,negated_conjecture,
% 0.23/0.57      v1_relat_1(sK2)).
% 0.23/0.57  
% 0.23/0.57  cnf(u38,axiom,
% 0.23/0.57      v1_relat_1(k2_zfmisc_1(X0,X1))).
% 0.23/0.57  
% 0.23/0.57  cnf(u34,axiom,
% 0.23/0.57      v1_xboole_0(k1_xboole_0)).
% 0.23/0.57  
% 0.23/0.57  cnf(u81,negated_conjecture,
% 0.23/0.57      ~v1_xboole_0(k1_relat_1(sK2))).
% 0.23/0.57  
% 0.23/0.57  cnf(u37,axiom,
% 0.23/0.57      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.23/0.57  
% 0.23/0.57  cnf(u63,negated_conjecture,
% 0.23/0.57      u1_struct_0(sK0) = k1_relat_1(sK2)).
% 0.23/0.57  
% 0.23/0.57  % (29049)# SZS output end Saturation.
% 0.23/0.57  % (29049)------------------------------
% 0.23/0.57  % (29049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (29049)Termination reason: Satisfiable
% 0.23/0.57  
% 0.23/0.57  % (29049)Memory used [KB]: 1663
% 0.23/0.57  % (29049)Time elapsed: 0.131 s
% 0.23/0.57  % (29049)------------------------------
% 0.23/0.57  % (29049)------------------------------
% 0.23/0.57  % (29044)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.57  % (29050)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.20/0.57  % (29031)Success in time 0.203 s
%------------------------------------------------------------------------------

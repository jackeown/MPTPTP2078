%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:23 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
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
cnf(u35,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u33,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u37,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u49,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u48,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u34,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u32,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u67,negated_conjecture,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

cnf(u78,negated_conjecture,
    ( v1_partfun1(sK2,k1_relat_1(sK2)) )).

cnf(u70,negated_conjecture,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK1) )).

cnf(u42,axiom,
    ( ~ v1_partfun1(X1,X0)
    | ~ v4_relat_1(X1,X0)
    | k1_relat_1(X1) = X0
    | ~ v1_relat_1(X1) )).

cnf(u69,negated_conjecture,
    ( v4_relat_1(sK2,k1_relat_1(sK2)) )).

cnf(u46,axiom,
    ( ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | v1_partfun1(X1,k1_relat_1(X1)) )).

cnf(u29,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u68,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u73,negated_conjecture,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

cnf(u47,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ v1_funct_1(X2)
    | v1_partfun1(X2,k1_xboole_0) )).

cnf(u43,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v4_relat_1(X2,X0) )).

cnf(u44,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_1(X2)
    | k1_xboole_0 = X1
    | v1_partfun1(X2,X0) )).

cnf(u38,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(X1) )).

cnf(u51,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u40,axiom,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) )).

cnf(u36,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u83,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(sK2)) )).

cnf(u39,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u65,negated_conjecture,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:08:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (13474)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (13478)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (13476)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (13488)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (13488)Refutation not found, incomplete strategy% (13488)------------------------------
% 0.22/0.50  % (13488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (13488)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (13488)Memory used [KB]: 6140
% 0.22/0.50  % (13488)Time elapsed: 0.058 s
% 0.22/0.50  % (13488)------------------------------
% 0.22/0.50  % (13488)------------------------------
% 0.22/0.50  % (13477)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (13476)Refutation not found, incomplete strategy% (13476)------------------------------
% 0.22/0.50  % (13476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (13483)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (13491)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (13484)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (13476)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13476)Memory used [KB]: 10746
% 0.22/0.51  % (13476)Time elapsed: 0.069 s
% 0.22/0.51  % (13476)------------------------------
% 0.22/0.51  % (13476)------------------------------
% 0.22/0.51  % (13483)Refutation not found, incomplete strategy% (13483)------------------------------
% 0.22/0.51  % (13483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13474)Refutation not found, incomplete strategy% (13474)------------------------------
% 0.22/0.51  % (13474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13474)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13474)Memory used [KB]: 10618
% 0.22/0.51  % (13474)Time elapsed: 0.077 s
% 0.22/0.51  % (13474)------------------------------
% 0.22/0.51  % (13474)------------------------------
% 0.22/0.51  % (13487)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (13482)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (13484)Refutation not found, incomplete strategy% (13484)------------------------------
% 0.22/0.51  % (13484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13484)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13484)Memory used [KB]: 10618
% 0.22/0.51  % (13484)Time elapsed: 0.081 s
% 0.22/0.51  % (13484)------------------------------
% 0.22/0.51  % (13484)------------------------------
% 0.22/0.51  % (13491)Refutation not found, incomplete strategy% (13491)------------------------------
% 0.22/0.51  % (13491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13491)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13491)Memory used [KB]: 1663
% 0.22/0.51  % (13491)Time elapsed: 0.082 s
% 0.22/0.51  % (13491)------------------------------
% 0.22/0.51  % (13491)------------------------------
% 0.22/0.51  % (13483)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13483)Memory used [KB]: 6268
% 0.22/0.51  % (13483)Time elapsed: 0.083 s
% 0.22/0.51  % (13483)------------------------------
% 0.22/0.51  % (13483)------------------------------
% 0.22/0.51  % (13489)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (13482)Refutation not found, incomplete strategy% (13482)------------------------------
% 0.22/0.51  % (13482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13482)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13482)Memory used [KB]: 10746
% 0.22/0.51  % (13482)Time elapsed: 0.093 s
% 0.22/0.51  % (13482)------------------------------
% 0.22/0.51  % (13482)------------------------------
% 0.22/0.51  % (13475)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.52  % (13475)Refutation not found, incomplete strategy% (13475)------------------------------
% 0.22/0.52  % (13475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13475)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (13475)Memory used [KB]: 10618
% 0.22/0.52  % (13475)Time elapsed: 0.063 s
% 0.22/0.52  % (13475)------------------------------
% 0.22/0.52  % (13475)------------------------------
% 0.22/0.52  % (13480)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (13473)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (13492)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.52  % (13485)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (13485)Refutation not found, incomplete strategy% (13485)------------------------------
% 0.22/0.52  % (13485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13485)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (13485)Memory used [KB]: 6012
% 0.22/0.52  % (13485)Time elapsed: 0.002 s
% 0.22/0.52  % (13485)------------------------------
% 0.22/0.52  % (13485)------------------------------
% 0.22/0.53  % (13486)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.53  % (13477)Refutation not found, incomplete strategy% (13477)------------------------------
% 0.22/0.53  % (13477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13477)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13477)Memory used [KB]: 1663
% 0.22/0.53  % (13477)Time elapsed: 0.105 s
% 0.22/0.53  % (13477)------------------------------
% 0.22/0.53  % (13477)------------------------------
% 0.22/0.53  % (13486)Refutation not found, incomplete strategy% (13486)------------------------------
% 0.22/0.53  % (13486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13486)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13486)Memory used [KB]: 1663
% 0.22/0.53  % (13486)Time elapsed: 0.071 s
% 0.22/0.53  % (13486)------------------------------
% 0.22/0.53  % (13486)------------------------------
% 0.22/0.53  % (13490)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.53  % (13473)Refutation not found, incomplete strategy% (13473)------------------------------
% 0.22/0.53  % (13473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13473)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13473)Memory used [KB]: 6140
% 0.22/0.53  % (13473)Time elapsed: 0.099 s
% 0.22/0.53  % (13473)------------------------------
% 0.22/0.53  % (13473)------------------------------
% 0.22/0.53  % (13481)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.53  % (13490)# SZS output start Saturation.
% 0.22/0.53  cnf(u35,negated_conjecture,
% 0.22/0.53      l1_orders_2(sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u33,negated_conjecture,
% 0.22/0.53      l1_orders_2(sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u37,axiom,
% 0.22/0.53      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u49,negated_conjecture,
% 0.22/0.53      l1_struct_0(sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u48,negated_conjecture,
% 0.22/0.53      l1_struct_0(sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u34,negated_conjecture,
% 0.22/0.53      ~v2_struct_0(sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u32,negated_conjecture,
% 0.22/0.53      ~v2_struct_0(sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u67,negated_conjecture,
% 0.22/0.53      v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))).
% 0.22/0.53  
% 0.22/0.53  cnf(u78,negated_conjecture,
% 0.22/0.53      v1_partfun1(sK2,k1_relat_1(sK2))).
% 0.22/0.53  
% 0.22/0.53  cnf(u70,negated_conjecture,
% 0.22/0.53      v1_partfun1(sK2,k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u42,axiom,
% 0.22/0.53      ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u69,negated_conjecture,
% 0.22/0.53      v4_relat_1(sK2,k1_relat_1(sK2))).
% 0.22/0.53  
% 0.22/0.53  cnf(u46,axiom,
% 0.22/0.53      ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1) | v1_partfun1(X1,k1_relat_1(X1))).
% 0.22/0.53  
% 0.22/0.53  cnf(u29,negated_conjecture,
% 0.22/0.53      v1_funct_1(sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u68,negated_conjecture,
% 0.22/0.53      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 0.22/0.53  
% 0.22/0.53  cnf(u73,negated_conjecture,
% 0.22/0.53      ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))).
% 0.22/0.53  
% 0.22/0.53  cnf(u47,axiom,
% 0.22/0.53      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,k1_xboole_0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u43,axiom,
% 0.22/0.53      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u44,axiom,
% 0.22/0.53      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k1_xboole_0 = X1 | v1_partfun1(X2,X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u38,axiom,
% 0.22/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u51,negated_conjecture,
% 0.22/0.53      v1_relat_1(sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u40,axiom,
% 0.22/0.53      v1_relat_1(k2_zfmisc_1(X0,X1))).
% 0.22/0.53  
% 0.22/0.53  cnf(u36,axiom,
% 0.22/0.53      v1_xboole_0(k1_xboole_0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u83,negated_conjecture,
% 0.22/0.53      ~v1_xboole_0(k1_relat_1(sK2))).
% 0.22/0.53  
% 0.22/0.53  cnf(u39,axiom,
% 0.22/0.53      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u65,negated_conjecture,
% 0.22/0.53      u1_struct_0(sK0) = k1_relat_1(sK2)).
% 0.22/0.53  
% 0.22/0.53  % (13490)# SZS output end Saturation.
% 0.22/0.53  % (13490)------------------------------
% 0.22/0.53  % (13490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13490)Termination reason: Satisfiable
% 0.22/0.53  
% 0.22/0.53  % (13490)Memory used [KB]: 1663
% 0.22/0.53  % (13490)Time elapsed: 0.105 s
% 0.22/0.53  % (13490)------------------------------
% 0.22/0.53  % (13490)------------------------------
% 0.22/0.53  % (13472)Success in time 0.166 s
%------------------------------------------------------------------------------

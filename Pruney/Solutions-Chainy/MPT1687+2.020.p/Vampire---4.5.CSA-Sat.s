%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:22 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   23 (  23 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    0
%              Number of atoms          :   45 (  45 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u28,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u26,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u30,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u45,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u44,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u27,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u25,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u60,negated_conjecture,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

cnf(u61,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u65,negated_conjecture,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

cnf(u43,axiom,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0
    | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) )).

cnf(u39,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
    | ~ v1_funct_2(X2,k1_xboole_0,X1) )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
    | v1_funct_2(X2,k1_xboole_0,X1) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | ~ v1_funct_2(X2,X0,k1_xboole_0) )).

cnf(u32,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) )).

cnf(u37,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1
    | k1_relset_1(X0,X1,X2) != X0
    | v1_funct_2(X2,X0,X1) )).

cnf(u38,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1
    | k1_relset_1(X0,X1,X2) = X0
    | ~ v1_funct_2(X2,X0,X1) )).

cnf(u22,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u29,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u71,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(sK2)) )).

cnf(u31,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u58,negated_conjecture,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) )).

cnf(u62,negated_conjecture,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:08:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (16834)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (16847)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (16847)Refutation not found, incomplete strategy% (16847)------------------------------
% 0.20/0.47  % (16847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (16839)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (16847)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (16847)Memory used [KB]: 1663
% 0.20/0.47  % (16847)Time elapsed: 0.006 s
% 0.20/0.47  % (16847)------------------------------
% 0.20/0.47  % (16847)------------------------------
% 0.20/0.48  % (16853)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.48  % (16834)Refutation not found, incomplete strategy% (16834)------------------------------
% 0.20/0.48  % (16834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (16834)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (16834)Memory used [KB]: 6140
% 0.20/0.48  % (16834)Time elapsed: 0.056 s
% 0.20/0.48  % (16834)------------------------------
% 0.20/0.48  % (16834)------------------------------
% 0.20/0.48  % (16853)Refutation not found, incomplete strategy% (16853)------------------------------
% 0.20/0.48  % (16853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (16853)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (16853)Memory used [KB]: 6140
% 0.20/0.48  % (16853)Time elapsed: 0.061 s
% 0.20/0.48  % (16853)------------------------------
% 0.20/0.48  % (16853)------------------------------
% 0.20/0.49  % (16837)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (16835)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (16842)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (16837)Refutation not found, incomplete strategy% (16837)------------------------------
% 0.20/0.49  % (16837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (16837)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (16837)Memory used [KB]: 10746
% 0.20/0.49  % (16837)Time elapsed: 0.087 s
% 0.20/0.49  % (16837)------------------------------
% 0.20/0.49  % (16837)------------------------------
% 0.20/0.49  % (16836)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (16846)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (16835)Refutation not found, incomplete strategy% (16835)------------------------------
% 0.20/0.50  % (16835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16835)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (16835)Memory used [KB]: 10618
% 0.20/0.50  % (16849)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (16835)Time elapsed: 0.087 s
% 0.20/0.50  % (16835)------------------------------
% 0.20/0.50  % (16835)------------------------------
% 0.20/0.50  % (16836)Refutation not found, incomplete strategy% (16836)------------------------------
% 0.20/0.50  % (16836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16836)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (16836)Memory used [KB]: 10618
% 0.20/0.50  % (16836)Time elapsed: 0.087 s
% 0.20/0.50  % (16836)------------------------------
% 0.20/0.50  % (16836)------------------------------
% 0.20/0.50  % (16850)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.50  % (16849)Refutation not found, incomplete strategy% (16849)------------------------------
% 0.20/0.50  % (16849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16849)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (16849)Memory used [KB]: 6140
% 0.20/0.50  % (16849)Time elapsed: 0.068 s
% 0.20/0.50  % (16849)------------------------------
% 0.20/0.50  % (16849)------------------------------
% 0.20/0.50  % (16838)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (16838)Refutation not found, incomplete strategy% (16838)------------------------------
% 0.20/0.50  % (16838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16838)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (16838)Memory used [KB]: 1663
% 0.20/0.50  % (16838)Time elapsed: 0.088 s
% 0.20/0.50  % (16838)------------------------------
% 0.20/0.50  % (16838)------------------------------
% 0.20/0.50  % (16841)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (16852)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (16850)Refutation not found, incomplete strategy% (16850)------------------------------
% 0.20/0.50  % (16850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16850)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (16850)Memory used [KB]: 10746
% 0.20/0.50  % (16850)Time elapsed: 0.090 s
% 0.20/0.50  % (16850)------------------------------
% 0.20/0.50  % (16850)------------------------------
% 0.20/0.50  % (16845)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (16844)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (16852)Refutation not found, incomplete strategy% (16852)------------------------------
% 0.20/0.50  % (16852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16852)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (16852)Memory used [KB]: 1663
% 0.20/0.50  % (16852)Time elapsed: 0.089 s
% 0.20/0.50  % (16852)------------------------------
% 0.20/0.50  % (16852)------------------------------
% 0.20/0.50  % (16840)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (16846)Refutation not found, incomplete strategy% (16846)------------------------------
% 0.20/0.50  % (16846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16846)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (16846)Memory used [KB]: 6012
% 0.20/0.50  % (16846)Time elapsed: 0.003 s
% 0.20/0.50  % (16846)------------------------------
% 0.20/0.50  % (16846)------------------------------
% 0.20/0.50  % (16845)Refutation not found, incomplete strategy% (16845)------------------------------
% 0.20/0.50  % (16845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16845)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (16845)Memory used [KB]: 10618
% 0.20/0.50  % (16845)Time elapsed: 0.102 s
% 0.20/0.50  % (16845)------------------------------
% 0.20/0.50  % (16845)------------------------------
% 0.20/0.50  % (16844)Refutation not found, incomplete strategy% (16844)------------------------------
% 0.20/0.50  % (16844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16844)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (16844)Memory used [KB]: 6140
% 0.20/0.50  % (16844)Time elapsed: 0.101 s
% 0.20/0.50  % (16844)------------------------------
% 0.20/0.50  % (16844)------------------------------
% 0.20/0.51  % (16851)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (16840)Refutation not found, incomplete strategy% (16840)------------------------------
% 0.20/0.51  % (16840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16840)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (16840)Memory used [KB]: 10746
% 0.20/0.51  % (16840)Time elapsed: 0.090 s
% 0.20/0.51  % (16840)------------------------------
% 0.20/0.51  % (16840)------------------------------
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.51  % (16851)# SZS output start Saturation.
% 0.20/0.51  cnf(u28,negated_conjecture,
% 0.20/0.51      l1_orders_2(sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u26,negated_conjecture,
% 0.20/0.51      l1_orders_2(sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u30,axiom,
% 0.20/0.51      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u45,negated_conjecture,
% 0.20/0.51      l1_struct_0(sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u44,negated_conjecture,
% 0.20/0.51      l1_struct_0(sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u27,negated_conjecture,
% 0.20/0.51      ~v2_struct_0(sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u25,negated_conjecture,
% 0.20/0.51      ~v2_struct_0(sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u60,negated_conjecture,
% 0.20/0.51      v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u61,negated_conjecture,
% 0.20/0.51      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 0.20/0.51  
% 0.20/0.51  cnf(u65,negated_conjecture,
% 0.20/0.51      ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))).
% 0.20/0.51  
% 0.20/0.51  cnf(u43,axiom,
% 0.20/0.51      ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u39,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u40,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u41,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u32,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u37,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u38,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u22,negated_conjecture,
% 0.20/0.51      v1_funct_1(sK2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u29,axiom,
% 0.20/0.51      v1_xboole_0(k1_xboole_0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u71,negated_conjecture,
% 0.20/0.51      ~v1_xboole_0(k1_relat_1(sK2))).
% 0.20/0.51  
% 0.20/0.51  cnf(u31,axiom,
% 0.20/0.51      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u58,negated_conjecture,
% 0.20/0.51      u1_struct_0(sK0) = k1_relat_1(sK2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u62,negated_conjecture,
% 0.20/0.51      k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)).
% 0.20/0.51  
% 0.20/0.51  % (16851)# SZS output end Saturation.
% 0.20/0.51  % (16851)------------------------------
% 0.20/0.51  % (16851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16851)Termination reason: Satisfiable
% 0.20/0.51  
% 0.20/0.51  % (16851)Memory used [KB]: 1663
% 0.20/0.51  % (16851)Time elapsed: 0.100 s
% 0.20/0.51  % (16851)------------------------------
% 0.20/0.51  % (16851)------------------------------
% 0.20/0.51  % (16854)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (16833)Success in time 0.146 s
%------------------------------------------------------------------------------

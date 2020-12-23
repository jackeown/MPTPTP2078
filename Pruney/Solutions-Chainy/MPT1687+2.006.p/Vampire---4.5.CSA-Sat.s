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
% DateTime   : Thu Dec  3 13:17:20 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   23 (  23 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    0
%              Number of atoms          :   41 (  41 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u31,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u29,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u32,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u41,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u40,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u30,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u28,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u57,negated_conjecture,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | v1_xboole_0(u1_struct_0(sK1)) )).

cnf(u64,negated_conjecture,
    ( v1_partfun1(sK2,k1_relat_1(sK2)) )).

cnf(u36,axiom,
    ( ~ v1_partfun1(X1,X0)
    | ~ v4_relat_1(X1,X0)
    | k1_relat_1(X1) = X0
    | ~ v1_relat_1(X1) )).

cnf(u54,negated_conjecture,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

cnf(u69,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(sK2)) )).

cnf(u33,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u56,negated_conjecture,
    ( v4_relat_1(sK2,k1_relat_1(sK2)) )).

cnf(u39,axiom,
    ( ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | v1_partfun1(X1,k1_relat_1(X1)) )).

cnf(u55,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u59,negated_conjecture,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

cnf(u37,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(X2) )).

cnf(u38,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v4_relat_1(X2,X0) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X0,X1)
    | v1_partfun1(X2,X0) )).

cnf(u25,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u42,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u52,negated_conjecture,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:50:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (28009)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (28010)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (28017)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (28017)Refutation not found, incomplete strategy% (28017)------------------------------
% 0.22/0.48  % (28017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (28017)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (28017)Memory used [KB]: 1663
% 0.22/0.48  % (28017)Time elapsed: 0.072 s
% 0.22/0.48  % (28017)------------------------------
% 0.22/0.48  % (28017)------------------------------
% 0.22/0.49  % (28023)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.49  % (28012)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (28014)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (28023)Refutation not found, incomplete strategy% (28023)------------------------------
% 0.22/0.49  % (28023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (28023)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (28023)Memory used [KB]: 6140
% 0.22/0.49  % (28023)Time elapsed: 0.074 s
% 0.22/0.49  % (28023)------------------------------
% 0.22/0.49  % (28023)------------------------------
% 0.22/0.49  % (28008)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (28011)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (28008)Refutation not found, incomplete strategy% (28008)------------------------------
% 0.22/0.50  % (28008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28008)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (28008)Memory used [KB]: 1663
% 0.22/0.50  % (28008)Time elapsed: 0.083 s
% 0.22/0.50  % (28008)------------------------------
% 0.22/0.50  % (28008)------------------------------
% 0.22/0.50  % (28018)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (28019)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (28019)Refutation not found, incomplete strategy% (28019)------------------------------
% 0.22/0.50  % (28019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28019)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (28019)Memory used [KB]: 6140
% 0.22/0.50  % (28019)Time elapsed: 0.049 s
% 0.22/0.50  % (28019)------------------------------
% 0.22/0.50  % (28019)------------------------------
% 0.22/0.50  % (28010)Refutation not found, incomplete strategy% (28010)------------------------------
% 0.22/0.50  % (28010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28010)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (28010)Memory used [KB]: 10618
% 0.22/0.50  % (28010)Time elapsed: 0.067 s
% 0.22/0.50  % (28010)------------------------------
% 0.22/0.50  % (28010)------------------------------
% 0.22/0.50  % (28004)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (28013)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (28004)Refutation not found, incomplete strategy% (28004)------------------------------
% 0.22/0.50  % (28004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28004)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (28004)Memory used [KB]: 6140
% 0.22/0.50  % (28004)Time elapsed: 0.081 s
% 0.22/0.50  % (28004)------------------------------
% 0.22/0.50  % (28004)------------------------------
% 0.22/0.50  % (28022)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (28024)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (28021)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % (28022)Refutation not found, incomplete strategy% (28022)------------------------------
% 0.22/0.50  % (28022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28022)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.51  % (28022)Memory used [KB]: 1663
% 0.22/0.51  % (28022)Time elapsed: 0.091 s
% 0.22/0.51  % (28022)------------------------------
% 0.22/0.51  % (28022)------------------------------
% 0.22/0.51  % (28024)Refutation not found, incomplete strategy% (28024)------------------------------
% 0.22/0.51  % (28024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28024)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (28024)Memory used [KB]: 10618
% 0.22/0.51  % (28024)Time elapsed: 0.097 s
% 0.22/0.51  % (28024)------------------------------
% 0.22/0.51  % (28024)------------------------------
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (28021)# SZS output start Saturation.
% 0.22/0.51  cnf(u31,negated_conjecture,
% 0.22/0.51      l1_orders_2(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u29,negated_conjecture,
% 0.22/0.51      l1_orders_2(sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u32,axiom,
% 0.22/0.51      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u41,negated_conjecture,
% 0.22/0.51      l1_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u40,negated_conjecture,
% 0.22/0.51      l1_struct_0(sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u30,negated_conjecture,
% 0.22/0.51      ~v2_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u28,negated_conjecture,
% 0.22/0.51      ~v2_struct_0(sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u57,negated_conjecture,
% 0.22/0.51      v1_partfun1(sK2,k1_relat_1(sK2)) | v1_xboole_0(u1_struct_0(sK1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u64,negated_conjecture,
% 0.22/0.51      v1_partfun1(sK2,k1_relat_1(sK2))).
% 0.22/0.51  
% 0.22/0.51  cnf(u36,axiom,
% 0.22/0.51      ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u54,negated_conjecture,
% 0.22/0.51      v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u69,negated_conjecture,
% 0.22/0.51      ~v1_xboole_0(k1_relat_1(sK2))).
% 0.22/0.51  
% 0.22/0.51  cnf(u33,axiom,
% 0.22/0.51      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u56,negated_conjecture,
% 0.22/0.51      v4_relat_1(sK2,k1_relat_1(sK2))).
% 0.22/0.51  
% 0.22/0.51  cnf(u39,axiom,
% 0.22/0.51      ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1) | v1_partfun1(X1,k1_relat_1(X1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u55,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 0.22/0.51  
% 0.22/0.51  cnf(u59,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))).
% 0.22/0.51  
% 0.22/0.51  cnf(u37,axiom,
% 0.22/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u38,axiom,
% 0.22/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u34,axiom,
% 0.22/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u25,negated_conjecture,
% 0.22/0.51      v1_funct_1(sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u42,negated_conjecture,
% 0.22/0.51      v1_relat_1(sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u52,negated_conjecture,
% 0.22/0.51      u1_struct_0(sK0) = k1_relat_1(sK2)).
% 0.22/0.51  
% 0.22/0.51  % (28021)# SZS output end Saturation.
% 0.22/0.51  % (28021)------------------------------
% 0.22/0.51  % (28021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28021)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (28021)Memory used [KB]: 1663
% 0.22/0.51  % (28021)Time elapsed: 0.088 s
% 0.22/0.51  % (28021)------------------------------
% 0.22/0.51  % (28021)------------------------------
% 0.22/0.51  % (28005)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (28003)Success in time 0.145 s
%------------------------------------------------------------------------------

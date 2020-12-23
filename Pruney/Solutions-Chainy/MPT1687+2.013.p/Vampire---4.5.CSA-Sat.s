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
% DateTime   : Thu Dec  3 13:17:21 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   43 (  43 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u37,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u35,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u42,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u52,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u51,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u36,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u34,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u32,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) )).

cnf(u30,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)) )).

cnf(u50,axiom,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) )).

cnf(u49,axiom,
    ( v1_partfun1(k6_relat_1(X0),X0) )).

cnf(u57,negated_conjecture,
    ( ~ v1_partfun1(sK2,X0)
    | k1_relat_1(sK2) = X0
    | ~ v4_relat_1(sK2,X0) )).

cnf(u56,axiom,
    ( v4_relat_1(k6_relat_1(X0),X0) )).

cnf(u55,negated_conjecture,
    ( v4_relat_1(sK2,u1_struct_0(sK0)) )).

cnf(u63,axiom,
    ( ~ v4_relat_1(k6_relat_1(X1),X2)
    | X1 = X2
    | ~ v1_partfun1(k6_relat_1(X1),X2) )).

cnf(u48,axiom,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )).

cnf(u33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )).

cnf(u46,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(X2) )).

cnf(u47,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v4_relat_1(X2,X0) )).

cnf(u31,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u54,axiom,
    ( v1_relat_1(k6_relat_1(X0)) )).

cnf(u53,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u45,axiom,
    ( ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X0)
    | k1_relat_1(X1) = X0
    | ~ v1_partfun1(X1,X0) )).

cnf(u38,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u43,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u62,axiom,
    ( k1_relat_1(k6_relat_1(X0)) = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:29:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (30700)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (30700)Refutation not found, incomplete strategy% (30700)------------------------------
% 0.22/0.53  % (30700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30700)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (30700)Memory used [KB]: 10618
% 0.22/0.53  % (30700)Time elapsed: 0.105 s
% 0.22/0.53  % (30700)------------------------------
% 0.22/0.53  % (30700)------------------------------
% 0.22/0.54  % (30717)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (30709)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (30717)Refutation not found, incomplete strategy% (30717)------------------------------
% 0.22/0.54  % (30717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30709)Refutation not found, incomplete strategy% (30709)------------------------------
% 0.22/0.54  % (30709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30709)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30709)Memory used [KB]: 10618
% 0.22/0.54  % (30709)Time elapsed: 0.070 s
% 0.22/0.54  % (30709)------------------------------
% 0.22/0.54  % (30709)------------------------------
% 0.22/0.54  % (30717)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30717)Memory used [KB]: 6268
% 0.22/0.54  % (30717)Time elapsed: 0.071 s
% 0.22/0.54  % (30717)------------------------------
% 0.22/0.54  % (30717)------------------------------
% 0.22/0.54  % (30698)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (30695)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.55  % (30698)# SZS output start Saturation.
% 0.22/0.55  cnf(u37,negated_conjecture,
% 0.22/0.55      l1_orders_2(sK0)).
% 0.22/0.55  
% 0.22/0.55  cnf(u35,negated_conjecture,
% 0.22/0.55      l1_orders_2(sK1)).
% 0.22/0.55  
% 0.22/0.55  cnf(u42,axiom,
% 0.22/0.55      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.22/0.55  
% 0.22/0.55  cnf(u52,negated_conjecture,
% 0.22/0.55      l1_struct_0(sK0)).
% 0.22/0.55  
% 0.22/0.55  cnf(u51,negated_conjecture,
% 0.22/0.55      l1_struct_0(sK1)).
% 0.22/0.55  
% 0.22/0.55  cnf(u36,negated_conjecture,
% 0.22/0.55      ~v2_struct_0(sK0)).
% 0.22/0.55  
% 0.22/0.55  cnf(u34,negated_conjecture,
% 0.22/0.55      ~v2_struct_0(sK1)).
% 0.22/0.55  
% 0.22/0.55  cnf(u32,negated_conjecture,
% 0.22/0.55      v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))).
% 0.22/0.55  
% 0.22/0.55  cnf(u30,negated_conjecture,
% 0.22/0.55      ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))).
% 0.22/0.55  
% 0.22/0.55  cnf(u50,axiom,
% 0.22/0.55      v1_partfun1(X1,k1_relat_1(X1)) | ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)).
% 0.22/0.55  
% 0.22/0.55  cnf(u49,axiom,
% 0.22/0.55      v1_partfun1(k6_relat_1(X0),X0)).
% 0.22/0.55  
% 0.22/0.55  cnf(u57,negated_conjecture,
% 0.22/0.55      ~v1_partfun1(sK2,X0) | k1_relat_1(sK2) = X0 | ~v4_relat_1(sK2,X0)).
% 0.22/0.55  
% 0.22/0.55  cnf(u56,axiom,
% 0.22/0.55      v4_relat_1(k6_relat_1(X0),X0)).
% 0.22/0.55  
% 0.22/0.55  cnf(u55,negated_conjecture,
% 0.22/0.55      v4_relat_1(sK2,u1_struct_0(sK0))).
% 0.22/0.55  
% 0.22/0.55  cnf(u63,axiom,
% 0.22/0.55      ~v4_relat_1(k6_relat_1(X1),X2) | X1 = X2 | ~v1_partfun1(k6_relat_1(X1),X2)).
% 0.22/0.55  
% 0.22/0.55  cnf(u48,axiom,
% 0.22/0.55      m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))).
% 0.22/0.55  
% 0.22/0.55  cnf(u33,negated_conjecture,
% 0.22/0.55      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))).
% 0.22/0.55  
% 0.22/0.55  cnf(u46,axiom,
% 0.22/0.55      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)).
% 0.22/0.55  
% 0.22/0.55  cnf(u47,axiom,
% 0.22/0.55      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)).
% 0.22/0.55  
% 0.22/0.55  cnf(u31,negated_conjecture,
% 0.22/0.55      v1_funct_1(sK2)).
% 0.22/0.55  
% 0.22/0.55  cnf(u54,axiom,
% 0.22/0.55      v1_relat_1(k6_relat_1(X0))).
% 0.22/0.55  
% 0.22/0.55  cnf(u53,negated_conjecture,
% 0.22/0.55      v1_relat_1(sK2)).
% 0.22/0.55  
% 0.22/0.55  cnf(u45,axiom,
% 0.22/0.55      ~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)).
% 0.22/0.55  
% 0.22/0.55  cnf(u38,axiom,
% 0.22/0.55      v1_xboole_0(k1_xboole_0)).
% 0.22/0.55  
% 0.22/0.55  cnf(u43,axiom,
% 0.22/0.55      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.22/0.55  
% 0.22/0.55  cnf(u62,axiom,
% 0.22/0.55      k1_relat_1(k6_relat_1(X0)) = X0).
% 0.22/0.55  
% 0.22/0.55  % (30698)# SZS output end Saturation.
% 0.22/0.55  % (30698)------------------------------
% 0.22/0.55  % (30698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (30698)Termination reason: Satisfiable
% 0.22/0.55  
% 0.22/0.55  % (30698)Memory used [KB]: 6268
% 0.22/0.55  % (30698)Time elapsed: 0.115 s
% 0.22/0.55  % (30698)------------------------------
% 0.22/0.55  % (30698)------------------------------
% 0.22/0.55  % (30707)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (30691)Success in time 0.174 s
%------------------------------------------------------------------------------

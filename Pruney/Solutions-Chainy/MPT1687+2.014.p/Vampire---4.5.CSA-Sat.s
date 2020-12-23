%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:21 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   24 (  24 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    0
%              Number of atoms          :   37 (  37 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u36,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u34,negated_conjecture,
    ( l1_orders_2(sK1) )).

% (9616)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
cnf(u40,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u48,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u47,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u35,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u33,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u31,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) )).

cnf(u38,axiom,
    ( v1_partfun1(k6_partfun1(X0),X0) )).

cnf(u43,axiom,
    ( ~ v1_partfun1(X1,X0)
    | ~ v4_relat_1(X1,X0)
    | k1_relat_1(X1) = X0
    | ~ v1_relat_1(X1) )).

cnf(u52,axiom,
    ( v4_relat_1(k6_partfun1(X0),X0) )).

cnf(u51,negated_conjecture,
    ( v4_relat_1(sK2,u1_struct_0(sK0)) )).

cnf(u46,axiom,
    ( ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | v1_partfun1(X1,k1_relat_1(X1)) )).

cnf(u39,axiom,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )).

cnf(u32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )).

cnf(u29,negated_conjecture,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)) )).

cnf(u44,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(X2) )).

cnf(u45,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v4_relat_1(X2,X0) )).

cnf(u30,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u50,axiom,
    ( v1_relat_1(k6_partfun1(X0)) )).

cnf(u49,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u37,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u41,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u55,axiom,
    ( k1_relat_1(k6_partfun1(X0)) = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:59:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (9621)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (9630)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.47  % (9621)Refutation not found, incomplete strategy% (9621)------------------------------
% 0.21/0.47  % (9621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9630)Refutation not found, incomplete strategy% (9630)------------------------------
% 0.21/0.48  % (9630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9630)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (9630)Memory used [KB]: 1663
% 0.21/0.48  % (9630)Time elapsed: 0.042 s
% 0.21/0.48  % (9630)------------------------------
% 0.21/0.48  % (9630)------------------------------
% 0.21/0.48  % (9621)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (9621)Memory used [KB]: 10618
% 0.21/0.48  % (9621)Time elapsed: 0.040 s
% 0.21/0.48  % (9621)------------------------------
% 0.21/0.48  % (9621)------------------------------
% 0.21/0.48  % (9627)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (9625)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (9617)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (9622)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (9625)Refutation not found, incomplete strategy% (9625)------------------------------
% 0.21/0.48  % (9625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9625)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (9625)Memory used [KB]: 1663
% 0.21/0.48  % (9625)Time elapsed: 0.053 s
% 0.21/0.48  % (9625)------------------------------
% 0.21/0.48  % (9625)------------------------------
% 0.21/0.48  % (9620)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (9622)Refutation not found, incomplete strategy% (9622)------------------------------
% 0.21/0.48  % (9622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9622)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (9622)Memory used [KB]: 6140
% 0.21/0.48  % (9622)Time elapsed: 0.047 s
% 0.21/0.48  % (9622)------------------------------
% 0.21/0.48  % (9622)------------------------------
% 0.21/0.48  % (9627)Refutation not found, incomplete strategy% (9627)------------------------------
% 0.21/0.48  % (9627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9627)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (9627)Memory used [KB]: 6140
% 0.21/0.48  % (9627)Time elapsed: 0.056 s
% 0.21/0.48  % (9627)------------------------------
% 0.21/0.48  % (9627)------------------------------
% 0.21/0.49  % (9623)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (9626)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (9623)Refutation not found, incomplete strategy% (9623)------------------------------
% 0.21/0.49  % (9623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9623)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (9623)Memory used [KB]: 10618
% 0.21/0.49  % (9623)Time elapsed: 0.065 s
% 0.21/0.49  % (9623)------------------------------
% 0.21/0.49  % (9623)------------------------------
% 0.21/0.49  % (9631)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (9628)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (9629)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (9631)Refutation not found, incomplete strategy% (9631)------------------------------
% 0.21/0.49  % (9631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9631)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (9631)Memory used [KB]: 6140
% 0.21/0.49  % (9631)Time elapsed: 0.062 s
% 0.21/0.49  % (9631)------------------------------
% 0.21/0.49  % (9631)------------------------------
% 0.21/0.49  % (9612)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (9629)# SZS output start Saturation.
% 0.21/0.49  cnf(u36,negated_conjecture,
% 0.21/0.49      l1_orders_2(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u34,negated_conjecture,
% 0.21/0.49      l1_orders_2(sK1)).
% 0.21/0.49  
% 0.21/0.49  % (9616)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  cnf(u40,axiom,
% 0.21/0.49      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u48,negated_conjecture,
% 0.21/0.49      l1_struct_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u47,negated_conjecture,
% 0.21/0.49      l1_struct_0(sK1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u35,negated_conjecture,
% 0.21/0.49      ~v2_struct_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u33,negated_conjecture,
% 0.21/0.49      ~v2_struct_0(sK1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u31,negated_conjecture,
% 0.21/0.49      v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))).
% 0.21/0.49  
% 0.21/0.49  cnf(u38,axiom,
% 0.21/0.49      v1_partfun1(k6_partfun1(X0),X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u43,axiom,
% 0.21/0.49      ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u52,axiom,
% 0.21/0.49      v4_relat_1(k6_partfun1(X0),X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u51,negated_conjecture,
% 0.21/0.49      v4_relat_1(sK2,u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u46,axiom,
% 0.21/0.49      ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1) | v1_partfun1(X1,k1_relat_1(X1))).
% 0.21/0.49  
% 0.21/0.49  cnf(u39,axiom,
% 0.21/0.49      m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))).
% 0.21/0.49  
% 0.21/0.49  cnf(u32,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))).
% 0.21/0.49  
% 0.21/0.49  cnf(u29,negated_conjecture,
% 0.21/0.49      ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))).
% 0.21/0.49  
% 0.21/0.49  cnf(u44,axiom,
% 0.21/0.49      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u45,axiom,
% 0.21/0.49      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u30,negated_conjecture,
% 0.21/0.49      v1_funct_1(sK2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u50,axiom,
% 0.21/0.49      v1_relat_1(k6_partfun1(X0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u49,negated_conjecture,
% 0.21/0.49      v1_relat_1(sK2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u37,axiom,
% 0.21/0.49      v1_xboole_0(k1_xboole_0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u41,axiom,
% 0.21/0.49      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u55,axiom,
% 0.21/0.49      k1_relat_1(k6_partfun1(X0)) = X0).
% 0.21/0.49  
% 0.21/0.49  % (9629)# SZS output end Saturation.
% 0.21/0.49  % (9629)------------------------------
% 0.21/0.49  % (9629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9629)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (9629)Memory used [KB]: 1663
% 0.21/0.49  % (9629)Time elapsed: 0.059 s
% 0.21/0.49  % (9629)------------------------------
% 0.21/0.49  % (9629)------------------------------
% 0.21/0.49  % (9612)Refutation not found, incomplete strategy% (9612)------------------------------
% 0.21/0.49  % (9612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9612)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (9612)Memory used [KB]: 6140
% 0.21/0.49  % (9612)Time elapsed: 0.061 s
% 0.21/0.49  % (9612)------------------------------
% 0.21/0.49  % (9612)------------------------------
% 0.21/0.49  % (9611)Success in time 0.132 s
%------------------------------------------------------------------------------

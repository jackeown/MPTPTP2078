%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:22 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   40 (  40 expanded)
%              Number of leaves         :   40 (  40 expanded)
%              Depth                    :    0
%              Number of atoms          :   76 (  76 expanded)
%              Number of equality atoms :   21 (  21 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u41,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u39,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u43,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u63,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u62,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u40,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u38,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u95,negated_conjecture,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

cnf(u111,axiom,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)
    | k1_xboole_0 = X0 )).

cnf(u61,axiom,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | k1_xboole_0 = X0 )).

cnf(u79,axiom,
    ( ~ v1_funct_2(k1_xboole_0,X1,X0)
    | k1_xboole_0 = X0
    | k1_relat_1(k1_xboole_0) = X1 )).

cnf(u70,axiom,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) )).

cnf(u35,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u97,negated_conjecture,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) )).

cnf(u64,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u47,axiom,
    ( ~ r1_tarski(X1,X0)
    | ~ r2_hidden(X0,X1) )).

cnf(u110,negated_conjecture,
    ( m1_subset_1(sK3(sK2),k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
    | v1_xboole_0(sK2) )).

cnf(u96,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u42,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u102,negated_conjecture,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

cnf(u56,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
    | ~ v1_funct_2(X2,k1_xboole_0,X1) )).

cnf(u57,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
    | v1_funct_2(X2,k1_xboole_0,X1) )).

cnf(u58,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | ~ v1_funct_2(X2,X0,k1_xboole_0) )).

cnf(u48,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) )).

cnf(u53,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1
    | k1_relset_1(X0,X1,X2) != X0
    | v1_funct_2(X2,X0,X1) )).

cnf(u54,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1
    | k1_relset_1(X0,X1,X2) = X0
    | ~ v1_funct_2(X2,X0,X1) )).

cnf(u46,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u66,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK3(X0),X1)
    | v1_xboole_0(X0) )).

cnf(u45,axiom,
    ( r2_hidden(sK3(X0),X0)
    | v1_xboole_0(X0) )).

cnf(u99,negated_conjecture,
    ( ~ r2_hidden(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),sK2) )).

cnf(u82,axiom,
    ( ~ r2_hidden(X0,k1_xboole_0) )).

cnf(u55,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2) )).

cnf(u84,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u115,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(sK2)) )).

cnf(u44,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u93,negated_conjecture,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) )).

cnf(u98,negated_conjecture,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) )).

cnf(u67,axiom,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) )).

cnf(u76,axiom,
    ( k1_relat_1(k1_xboole_0) != X1
    | k1_xboole_0 = X0
    | v1_funct_2(k1_xboole_0,X1,X0) )).

cnf(u72,axiom,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:52:31 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (8586)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (8585)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (8584)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (8594)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (8594)Refutation not found, incomplete strategy% (8594)------------------------------
% 0.22/0.49  % (8594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8594)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (8594)Memory used [KB]: 6140
% 0.22/0.49  % (8594)Time elapsed: 0.069 s
% 0.22/0.49  % (8594)------------------------------
% 0.22/0.49  % (8594)------------------------------
% 0.22/0.49  % (8585)Refutation not found, incomplete strategy% (8585)------------------------------
% 0.22/0.49  % (8585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8593)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (8592)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (8585)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (8585)Memory used [KB]: 10746
% 0.22/0.50  % (8585)Time elapsed: 0.063 s
% 0.22/0.50  % (8585)------------------------------
% 0.22/0.50  % (8585)------------------------------
% 0.22/0.50  % (8592)Refutation not found, incomplete strategy% (8592)------------------------------
% 0.22/0.50  % (8592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (8592)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (8592)Memory used [KB]: 1663
% 0.22/0.50  % (8592)Time elapsed: 0.077 s
% 0.22/0.50  % (8592)------------------------------
% 0.22/0.50  % (8592)------------------------------
% 0.22/0.50  % (8588)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (8579)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (8581)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (8595)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (8588)Refutation not found, incomplete strategy% (8588)------------------------------
% 0.22/0.51  % (8588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8588)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8588)Memory used [KB]: 10746
% 0.22/0.51  % (8588)Time elapsed: 0.048 s
% 0.22/0.51  % (8588)------------------------------
% 0.22/0.51  % (8588)------------------------------
% 0.22/0.51  % (8596)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (8581)Refutation not found, incomplete strategy% (8581)------------------------------
% 0.22/0.51  % (8581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8581)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8581)Memory used [KB]: 10618
% 0.22/0.51  % (8581)Time elapsed: 0.090 s
% 0.22/0.51  % (8581)------------------------------
% 0.22/0.51  % (8581)------------------------------
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (8596)# SZS output start Saturation.
% 0.22/0.51  cnf(u41,negated_conjecture,
% 0.22/0.51      l1_orders_2(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u39,negated_conjecture,
% 0.22/0.51      l1_orders_2(sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u43,axiom,
% 0.22/0.51      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u63,negated_conjecture,
% 0.22/0.51      l1_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u62,negated_conjecture,
% 0.22/0.51      l1_struct_0(sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u40,negated_conjecture,
% 0.22/0.51      ~v2_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u38,negated_conjecture,
% 0.22/0.51      ~v2_struct_0(sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u95,negated_conjecture,
% 0.22/0.51      v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u111,axiom,
% 0.22/0.51      v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0) | k1_xboole_0 = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u61,axiom,
% 0.22/0.51      v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u79,axiom,
% 0.22/0.51      ~v1_funct_2(k1_xboole_0,X1,X0) | k1_xboole_0 = X0 | k1_relat_1(k1_xboole_0) = X1).
% 0.22/0.51  
% 0.22/0.51  cnf(u70,axiom,
% 0.22/0.51      ~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 = k1_relat_1(k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u35,negated_conjecture,
% 0.22/0.51      v1_funct_1(sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u97,negated_conjecture,
% 0.22/0.51      r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))).
% 0.22/0.51  
% 0.22/0.51  cnf(u64,axiom,
% 0.22/0.51      r1_tarski(k1_xboole_0,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u47,axiom,
% 0.22/0.51      ~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u110,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK3(sK2),k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) | v1_xboole_0(sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u96,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 0.22/0.51  
% 0.22/0.51  cnf(u42,axiom,
% 0.22/0.51      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u102,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))).
% 0.22/0.51  
% 0.22/0.51  cnf(u56,axiom,
% 0.22/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u57,axiom,
% 0.22/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u58,axiom,
% 0.22/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u48,axiom,
% 0.22/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u53,axiom,
% 0.22/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u54,axiom,
% 0.22/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u46,axiom,
% 0.22/0.51      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u66,axiom,
% 0.22/0.51      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK3(X0),X1) | v1_xboole_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u45,axiom,
% 0.22/0.51      r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u99,negated_conjecture,
% 0.22/0.51      ~r2_hidden(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u82,axiom,
% 0.22/0.51      ~r2_hidden(X0,k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u55,axiom,
% 0.22/0.51      ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u84,axiom,
% 0.22/0.51      v1_xboole_0(k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u115,negated_conjecture,
% 0.22/0.51      ~v1_xboole_0(k1_relat_1(sK2))).
% 0.22/0.51  
% 0.22/0.51  cnf(u44,axiom,
% 0.22/0.51      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u93,negated_conjecture,
% 0.22/0.51      u1_struct_0(sK0) = k1_relat_1(sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u98,negated_conjecture,
% 0.22/0.51      k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u67,axiom,
% 0.22/0.51      k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u76,axiom,
% 0.22/0.51      k1_relat_1(k1_xboole_0) != X1 | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X1,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u72,axiom,
% 0.22/0.51      k1_xboole_0 != k1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)).
% 0.22/0.51  
% 0.22/0.51  % (8596)# SZS output end Saturation.
% 0.22/0.51  % (8596)------------------------------
% 0.22/0.51  % (8596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8596)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (8596)Memory used [KB]: 1663
% 0.22/0.51  % (8596)Time elapsed: 0.062 s
% 0.22/0.51  % (8596)------------------------------
% 0.22/0.51  % (8596)------------------------------
% 0.22/0.51  % (8578)Success in time 0.144 s
%------------------------------------------------------------------------------

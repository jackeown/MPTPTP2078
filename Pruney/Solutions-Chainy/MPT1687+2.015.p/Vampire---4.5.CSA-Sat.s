%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
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
cnf(u34,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u32,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u36,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u47,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u46,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u33,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u31,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u64,negated_conjecture,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

cnf(u67,negated_conjecture,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK1) )).

cnf(u75,negated_conjecture,
    ( v1_partfun1(sK2,k1_relat_1(sK2)) )).

cnf(u39,axiom,
    ( ~ v1_partfun1(X1,X0)
    | ~ v4_relat_1(X1,X0)
    | k1_relat_1(X1) = X0
    | ~ v1_relat_1(X1) )).

cnf(u66,negated_conjecture,
    ( v4_relat_1(sK2,k1_relat_1(sK2)) )).

cnf(u44,axiom,
    ( ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | v1_partfun1(X1,k1_relat_1(X1)) )).

cnf(u65,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u70,negated_conjecture,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

cnf(u45,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ v1_funct_1(X2)
    | v1_partfun1(X2,k1_xboole_0) )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(X2) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v4_relat_1(X2,X0) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_1(X2)
    | k1_xboole_0 = X1
    | v1_partfun1(X2,X0) )).

cnf(u28,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u48,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u35,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u80,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(sK2)) )).

cnf(u37,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u62,negated_conjecture,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:54:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (26488)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (26490)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (26488)Refutation not found, incomplete strategy% (26488)------------------------------
% 0.22/0.48  % (26488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (26496)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.48  % (26488)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (26488)Memory used [KB]: 10746
% 0.22/0.48  % (26488)Time elapsed: 0.059 s
% 0.22/0.48  % (26488)------------------------------
% 0.22/0.48  % (26488)------------------------------
% 0.22/0.48  % (26496)Refutation not found, incomplete strategy% (26496)------------------------------
% 0.22/0.48  % (26496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (26496)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (26496)Memory used [KB]: 10618
% 0.22/0.48  % (26496)Time elapsed: 0.071 s
% 0.22/0.48  % (26496)------------------------------
% 0.22/0.48  % (26496)------------------------------
% 0.22/0.49  % (26499)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (26486)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (26500)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (26493)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (26500)Refutation not found, incomplete strategy% (26500)------------------------------
% 0.22/0.49  % (26500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (26500)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (26500)Memory used [KB]: 6140
% 0.22/0.49  % (26500)Time elapsed: 0.034 s
% 0.22/0.49  % (26500)------------------------------
% 0.22/0.49  % (26500)------------------------------
% 0.22/0.49  % (26486)Refutation not found, incomplete strategy% (26486)------------------------------
% 0.22/0.49  % (26486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (26486)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (26486)Memory used [KB]: 10618
% 0.22/0.49  % (26486)Time elapsed: 0.069 s
% 0.22/0.49  % (26486)------------------------------
% 0.22/0.49  % (26486)------------------------------
% 0.22/0.50  % (26503)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.50  % (26503)# SZS output start Saturation.
% 0.22/0.50  cnf(u34,negated_conjecture,
% 0.22/0.50      l1_orders_2(sK0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u32,negated_conjecture,
% 0.22/0.50      l1_orders_2(sK1)).
% 0.22/0.50  
% 0.22/0.50  cnf(u36,axiom,
% 0.22/0.50      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u47,negated_conjecture,
% 0.22/0.50      l1_struct_0(sK0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u46,negated_conjecture,
% 0.22/0.50      l1_struct_0(sK1)).
% 0.22/0.50  
% 0.22/0.50  cnf(u33,negated_conjecture,
% 0.22/0.50      ~v2_struct_0(sK0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u31,negated_conjecture,
% 0.22/0.50      ~v2_struct_0(sK1)).
% 0.22/0.50  
% 0.22/0.50  cnf(u64,negated_conjecture,
% 0.22/0.50      v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))).
% 0.22/0.50  
% 0.22/0.50  cnf(u67,negated_conjecture,
% 0.22/0.50      v1_partfun1(sK2,k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK1)).
% 0.22/0.50  
% 0.22/0.50  cnf(u75,negated_conjecture,
% 0.22/0.50      v1_partfun1(sK2,k1_relat_1(sK2))).
% 0.22/0.50  
% 0.22/0.50  cnf(u39,axiom,
% 0.22/0.50      ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)).
% 0.22/0.50  
% 0.22/0.50  cnf(u66,negated_conjecture,
% 0.22/0.50      v4_relat_1(sK2,k1_relat_1(sK2))).
% 0.22/0.50  
% 0.22/0.50  cnf(u44,axiom,
% 0.22/0.50      ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1) | v1_partfun1(X1,k1_relat_1(X1))).
% 0.22/0.50  
% 0.22/0.50  cnf(u65,negated_conjecture,
% 0.22/0.50      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 0.22/0.50  
% 0.22/0.50  cnf(u70,negated_conjecture,
% 0.22/0.50      ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))).
% 0.22/0.50  
% 0.22/0.50  cnf(u45,axiom,
% 0.22/0.50      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,k1_xboole_0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u40,axiom,
% 0.22/0.50      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)).
% 0.22/0.50  
% 0.22/0.50  cnf(u41,axiom,
% 0.22/0.50      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u42,axiom,
% 0.22/0.50      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k1_xboole_0 = X1 | v1_partfun1(X2,X0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u28,negated_conjecture,
% 0.22/0.50      v1_funct_1(sK2)).
% 0.22/0.50  
% 0.22/0.50  cnf(u48,negated_conjecture,
% 0.22/0.50      v1_relat_1(sK2)).
% 0.22/0.50  
% 0.22/0.50  cnf(u35,axiom,
% 0.22/0.50      v1_xboole_0(k1_xboole_0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u80,negated_conjecture,
% 0.22/0.50      ~v1_xboole_0(k1_relat_1(sK2))).
% 0.22/0.50  
% 0.22/0.50  cnf(u37,axiom,
% 0.22/0.50      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u62,negated_conjecture,
% 0.22/0.50      u1_struct_0(sK0) = k1_relat_1(sK2)).
% 0.22/0.50  
% 0.22/0.50  % (26503)# SZS output end Saturation.
% 0.22/0.50  % (26503)------------------------------
% 0.22/0.50  % (26503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26503)Termination reason: Satisfiable
% 0.22/0.50  
% 0.22/0.50  % (26503)Memory used [KB]: 1663
% 0.22/0.50  % (26503)Time elapsed: 0.082 s
% 0.22/0.50  % (26503)------------------------------
% 0.22/0.50  % (26503)------------------------------
% 0.22/0.50  % (26491)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (26484)Success in time 0.137 s
%------------------------------------------------------------------------------

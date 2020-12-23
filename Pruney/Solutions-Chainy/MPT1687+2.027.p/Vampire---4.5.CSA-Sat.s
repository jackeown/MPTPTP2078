%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:23 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   24 (  24 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    0
%              Number of atoms          :   43 (  43 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u34,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u32,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u35,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u45,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u44,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u33,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u31,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u62,negated_conjecture,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | v1_xboole_0(u1_struct_0(sK1)) )).

cnf(u69,negated_conjecture,
    ( v1_partfun1(sK2,k1_relat_1(sK2)) )).

cnf(u41,axiom,
    ( ~ v1_partfun1(X1,X0)
    | ~ v4_relat_1(X1,X0)
    | k1_relat_1(X1) = X0
    | ~ v1_relat_1(X1) )).

cnf(u59,negated_conjecture,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

cnf(u74,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(sK2)) )).

cnf(u37,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u61,negated_conjecture,
    ( v4_relat_1(sK2,k1_relat_1(sK2)) )).

cnf(u43,axiom,
    ( ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | v1_partfun1(X1,k1_relat_1(X1)) )).

cnf(u28,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u60,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u64,negated_conjecture,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v4_relat_1(X2,X0) )).

cnf(u39,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X0,X1)
    | v1_partfun1(X2,X0) )).

cnf(u36,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(X1) )).

cnf(u47,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u38,axiom,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) )).

cnf(u57,negated_conjecture,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (28820)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (28826)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (28826)Refutation not found, incomplete strategy% (28826)------------------------------
% 0.20/0.47  % (28826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (28826)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (28826)Memory used [KB]: 6012
% 0.20/0.47  % (28826)Time elapsed: 0.002 s
% 0.20/0.47  % (28826)------------------------------
% 0.20/0.47  % (28826)------------------------------
% 0.20/0.47  % (28828)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (28817)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (28818)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (28818)Refutation not found, incomplete strategy% (28818)------------------------------
% 0.20/0.48  % (28818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (28818)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (28818)Memory used [KB]: 1663
% 0.20/0.48  % (28818)Time elapsed: 0.064 s
% 0.20/0.48  % (28818)------------------------------
% 0.20/0.48  % (28818)------------------------------
% 0.20/0.48  % (28820)Refutation not found, incomplete strategy% (28820)------------------------------
% 0.20/0.48  % (28820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (28820)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (28820)Memory used [KB]: 10618
% 0.20/0.48  % (28820)Time elapsed: 0.062 s
% 0.20/0.48  % (28820)------------------------------
% 0.20/0.48  % (28820)------------------------------
% 0.20/0.48  % (28825)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (28825)Refutation not found, incomplete strategy% (28825)------------------------------
% 0.20/0.48  % (28825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (28825)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (28825)Memory used [KB]: 10618
% 0.20/0.48  % (28825)Time elapsed: 0.073 s
% 0.20/0.48  % (28825)------------------------------
% 0.20/0.48  % (28825)------------------------------
% 0.20/0.48  % (28817)Refutation not found, incomplete strategy% (28817)------------------------------
% 0.20/0.48  % (28817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (28817)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (28817)Memory used [KB]: 10746
% 0.20/0.48  % (28817)Time elapsed: 0.062 s
% 0.20/0.48  % (28817)------------------------------
% 0.20/0.48  % (28817)------------------------------
% 0.20/0.48  % (28819)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (28827)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (28831)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (28827)Refutation not found, incomplete strategy% (28827)------------------------------
% 0.20/0.49  % (28827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (28827)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (28827)Memory used [KB]: 1663
% 0.20/0.49  % (28827)Time elapsed: 0.085 s
% 0.20/0.49  % (28827)------------------------------
% 0.20/0.49  % (28827)------------------------------
% 0.20/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.49  % (28831)# SZS output start Saturation.
% 0.20/0.49  cnf(u34,negated_conjecture,
% 0.20/0.49      l1_orders_2(sK0)).
% 0.20/0.49  
% 0.20/0.49  cnf(u32,negated_conjecture,
% 0.20/0.49      l1_orders_2(sK1)).
% 0.20/0.49  
% 0.20/0.49  cnf(u35,axiom,
% 0.20/0.49      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.20/0.49  
% 0.20/0.49  cnf(u45,negated_conjecture,
% 0.20/0.49      l1_struct_0(sK0)).
% 0.20/0.49  
% 0.20/0.49  cnf(u44,negated_conjecture,
% 0.20/0.49      l1_struct_0(sK1)).
% 0.20/0.49  
% 0.20/0.49  cnf(u33,negated_conjecture,
% 0.20/0.49      ~v2_struct_0(sK0)).
% 0.20/0.49  
% 0.20/0.49  cnf(u31,negated_conjecture,
% 0.20/0.49      ~v2_struct_0(sK1)).
% 0.20/0.49  
% 0.20/0.49  cnf(u62,negated_conjecture,
% 0.20/0.49      v1_partfun1(sK2,k1_relat_1(sK2)) | v1_xboole_0(u1_struct_0(sK1))).
% 0.20/0.49  
% 0.20/0.49  cnf(u69,negated_conjecture,
% 0.20/0.49      v1_partfun1(sK2,k1_relat_1(sK2))).
% 0.20/0.49  
% 0.20/0.49  cnf(u41,axiom,
% 0.20/0.49      ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)).
% 0.20/0.49  
% 0.20/0.49  cnf(u59,negated_conjecture,
% 0.20/0.49      v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))).
% 0.20/0.49  
% 0.20/0.49  cnf(u74,negated_conjecture,
% 0.20/0.49      ~v1_xboole_0(k1_relat_1(sK2))).
% 0.20/0.49  
% 0.20/0.49  cnf(u37,axiom,
% 0.20/0.49      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.20/0.49  
% 0.20/0.49  cnf(u61,negated_conjecture,
% 0.20/0.49      v4_relat_1(sK2,k1_relat_1(sK2))).
% 0.20/0.49  
% 0.20/0.49  cnf(u43,axiom,
% 0.20/0.49      ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1) | v1_partfun1(X1,k1_relat_1(X1))).
% 0.20/0.49  
% 0.20/0.49  cnf(u28,negated_conjecture,
% 0.20/0.49      v1_funct_1(sK2)).
% 0.20/0.49  
% 0.20/0.49  cnf(u60,negated_conjecture,
% 0.20/0.49      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 0.20/0.49  
% 0.20/0.49  cnf(u64,negated_conjecture,
% 0.20/0.49      ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))).
% 0.20/0.49  
% 0.20/0.49  cnf(u42,axiom,
% 0.20/0.49      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)).
% 0.20/0.49  
% 0.20/0.49  cnf(u39,axiom,
% 0.20/0.49      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)).
% 0.20/0.49  
% 0.20/0.49  cnf(u36,axiom,
% 0.20/0.49      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)).
% 0.20/0.49  
% 0.20/0.49  cnf(u47,negated_conjecture,
% 0.20/0.49      v1_relat_1(sK2)).
% 0.20/0.49  
% 0.20/0.49  cnf(u38,axiom,
% 0.20/0.49      v1_relat_1(k2_zfmisc_1(X0,X1))).
% 0.20/0.49  
% 0.20/0.49  cnf(u57,negated_conjecture,
% 0.20/0.49      u1_struct_0(sK0) = k1_relat_1(sK2)).
% 0.20/0.49  
% 0.20/0.49  % (28831)# SZS output end Saturation.
% 0.20/0.49  % (28831)------------------------------
% 0.20/0.49  % (28831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (28831)Termination reason: Satisfiable
% 0.20/0.49  
% 0.20/0.49  % (28831)Memory used [KB]: 1663
% 0.20/0.49  % (28831)Time elapsed: 0.086 s
% 0.20/0.49  % (28831)------------------------------
% 0.20/0.49  % (28831)------------------------------
% 0.20/0.50  % (28834)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (28809)Success in time 0.136 s
%------------------------------------------------------------------------------

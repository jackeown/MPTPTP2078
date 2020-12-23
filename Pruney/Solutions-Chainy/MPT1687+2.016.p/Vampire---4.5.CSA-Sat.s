%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:21 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   41 (  41 expanded)
%              Number of leaves         :   41 (  41 expanded)
%              Depth                    :    0
%              Number of atoms          :   81 (  81 expanded)
%              Number of equality atoms :   30 (  30 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u38,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u36,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u40,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u59,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u58,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u37,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u35,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u98,negated_conjecture,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

cnf(u114,axiom,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)
    | k1_xboole_0 = X0 )).

cnf(u57,axiom,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | k1_xboole_0 = X0 )).

cnf(u87,axiom,
    ( ~ v1_funct_2(sK3(X3,X2),X3,X2)
    | k1_xboole_0 = X2
    | k1_relat_1(sK3(X3,X2)) = X3 )).

cnf(u75,axiom,
    ( ~ v1_funct_2(sK3(X1,k1_xboole_0),X1,k1_xboole_0)
    | k1_xboole_0 = sK3(X1,k1_xboole_0)
    | k1_xboole_0 = X1 )).

cnf(u69,axiom,
    ( ~ v1_funct_2(sK3(k1_xboole_0,X1),k1_xboole_0,X1)
    | k1_xboole_0 = k1_relat_1(sK3(k1_xboole_0,X1)) )).

cnf(u84,axiom,
    ( ~ v1_funct_2(k1_xboole_0,X1,X0)
    | k1_xboole_0 = X0
    | k1_relat_1(k1_xboole_0) = X1 )).

cnf(u68,axiom,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) )).

cnf(u88,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u44,axiom,
    ( v1_xboole_0(sK3(X0,X1)) )).

cnf(u100,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | v1_xboole_0(sK2) )).

cnf(u113,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(sK2)) )).

cnf(u60,axiom,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_xboole_0) )).

cnf(u41,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u32,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u99,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u43,axiom,
    ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )).

cnf(u39,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u104,negated_conjecture,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

cnf(u52,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
    | ~ v1_funct_2(X2,k1_xboole_0,X1) )).

cnf(u53,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
    | v1_funct_2(X2,k1_xboole_0,X1) )).

cnf(u54,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | ~ v1_funct_2(X2,X0,k1_xboole_0) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X2) )).

cnf(u45,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) )).

cnf(u50,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1
    | k1_relset_1(X0,X1,X2) != X0
    | v1_funct_2(X2,X0,X1) )).

cnf(u51,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1
    | k1_relset_1(X0,X1,X2) = X0
    | ~ v1_funct_2(X2,X0,X1) )).

cnf(u96,negated_conjecture,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) )).

cnf(u101,negated_conjecture,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) )).

cnf(u65,axiom,
    ( k1_relset_1(X2,X3,sK3(X2,X3)) = k1_relat_1(sK3(X2,X3)) )).

cnf(u63,axiom,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) )).

cnf(u80,axiom,
    ( k1_relat_1(sK3(X3,X2)) != X3
    | k1_xboole_0 = X2
    | v1_funct_2(sK3(X3,X2),X3,X2) )).

cnf(u79,axiom,
    ( k1_relat_1(k1_xboole_0) != X1
    | k1_xboole_0 = X0
    | v1_funct_2(k1_xboole_0,X1,X0) )).

cnf(u73,axiom,
    ( k1_xboole_0 != k1_relat_1(sK3(k1_xboole_0,X1))
    | v1_funct_2(sK3(k1_xboole_0,X1),k1_xboole_0,X1) )).

cnf(u72,axiom,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (28416)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (28411)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (28414)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (28415)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (28412)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (28425)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (28416)Refutation not found, incomplete strategy% (28416)------------------------------
% 0.20/0.48  % (28416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (28416)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (28416)Memory used [KB]: 10746
% 0.20/0.48  % (28416)Time elapsed: 0.076 s
% 0.20/0.48  % (28416)------------------------------
% 0.20/0.48  % (28416)------------------------------
% 0.20/0.48  % (28417)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (28413)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (28425)Refutation not found, incomplete strategy% (28425)------------------------------
% 0.20/0.49  % (28425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (28425)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (28425)Memory used [KB]: 6140
% 0.20/0.49  % (28425)Time elapsed: 0.030 s
% 0.20/0.49  % (28425)------------------------------
% 0.20/0.49  % (28425)------------------------------
% 0.20/0.49  % (28428)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.49  % (28411)Refutation not found, incomplete strategy% (28411)------------------------------
% 0.20/0.49  % (28411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (28411)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (28411)Memory used [KB]: 10618
% 0.20/0.49  % (28411)Time elapsed: 0.080 s
% 0.20/0.49  % (28411)------------------------------
% 0.20/0.49  % (28411)------------------------------
% 0.20/0.49  % (28424)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (28420)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.49  % (28428)Refutation not found, incomplete strategy% (28428)------------------------------
% 0.20/0.49  % (28428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (28428)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (28428)Memory used [KB]: 1663
% 0.20/0.49  % (28428)Time elapsed: 0.083 s
% 0.20/0.49  % (28428)------------------------------
% 0.20/0.49  % (28428)------------------------------
% 0.20/0.49  % (28423)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (28412)Refutation not found, incomplete strategy% (28412)------------------------------
% 0.20/0.49  % (28412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (28412)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (28412)Memory used [KB]: 10618
% 0.20/0.49  % (28412)Time elapsed: 0.073 s
% 0.20/0.49  % (28412)------------------------------
% 0.20/0.49  % (28412)------------------------------
% 0.20/0.49  % (28421)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (28429)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (28430)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (28421)Refutation not found, incomplete strategy% (28421)------------------------------
% 0.20/0.50  % (28421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (28413)Refutation not found, incomplete strategy% (28413)------------------------------
% 0.20/0.50  % (28413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (28413)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (28413)Memory used [KB]: 10874
% 0.20/0.50  % (28413)Time elapsed: 0.077 s
% 0.20/0.50  % (28419)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (28413)------------------------------
% 0.20/0.50  % (28413)------------------------------
% 0.20/0.50  % (28430)Refutation not found, incomplete strategy% (28430)------------------------------
% 0.20/0.50  % (28430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (28430)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (28430)Memory used [KB]: 10618
% 0.20/0.50  % (28430)Time elapsed: 0.095 s
% 0.20/0.50  % (28430)------------------------------
% 0.20/0.50  % (28430)------------------------------
% 0.20/0.50  % (28421)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (28421)Memory used [KB]: 10618
% 0.20/0.50  % (28421)Time elapsed: 0.094 s
% 0.20/0.50  % (28421)------------------------------
% 0.20/0.50  % (28421)------------------------------
% 0.20/0.50  % (28427)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.51  % (28427)# SZS output start Saturation.
% 0.20/0.51  cnf(u38,negated_conjecture,
% 0.20/0.51      l1_orders_2(sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u36,negated_conjecture,
% 0.20/0.51      l1_orders_2(sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u40,axiom,
% 0.20/0.51      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u59,negated_conjecture,
% 0.20/0.51      l1_struct_0(sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u58,negated_conjecture,
% 0.20/0.51      l1_struct_0(sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u37,negated_conjecture,
% 0.20/0.51      ~v2_struct_0(sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u35,negated_conjecture,
% 0.20/0.51      ~v2_struct_0(sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u98,negated_conjecture,
% 0.20/0.51      v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u114,axiom,
% 0.20/0.51      v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0) | k1_xboole_0 = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u57,axiom,
% 0.20/0.51      v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u87,axiom,
% 0.20/0.51      ~v1_funct_2(sK3(X3,X2),X3,X2) | k1_xboole_0 = X2 | k1_relat_1(sK3(X3,X2)) = X3).
% 0.20/0.51  
% 0.20/0.51  cnf(u75,axiom,
% 0.20/0.51      ~v1_funct_2(sK3(X1,k1_xboole_0),X1,k1_xboole_0) | k1_xboole_0 = sK3(X1,k1_xboole_0) | k1_xboole_0 = X1).
% 0.20/0.51  
% 0.20/0.51  cnf(u69,axiom,
% 0.20/0.51      ~v1_funct_2(sK3(k1_xboole_0,X1),k1_xboole_0,X1) | k1_xboole_0 = k1_relat_1(sK3(k1_xboole_0,X1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u84,axiom,
% 0.20/0.51      ~v1_funct_2(k1_xboole_0,X1,X0) | k1_xboole_0 = X0 | k1_relat_1(k1_xboole_0) = X1).
% 0.20/0.51  
% 0.20/0.51  cnf(u68,axiom,
% 0.20/0.51      ~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 = k1_relat_1(k1_xboole_0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u88,axiom,
% 0.20/0.51      v1_xboole_0(k1_xboole_0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u44,axiom,
% 0.20/0.51      v1_xboole_0(sK3(X0,X1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u100,negated_conjecture,
% 0.20/0.51      ~v1_xboole_0(k1_relat_1(sK2)) | v1_xboole_0(sK2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u113,negated_conjecture,
% 0.20/0.51      ~v1_xboole_0(k1_relat_1(sK2))).
% 0.20/0.51  
% 0.20/0.51  cnf(u60,axiom,
% 0.20/0.51      ~v1_xboole_0(X0) | v1_xboole_0(k1_xboole_0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u41,axiom,
% 0.20/0.51      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u32,negated_conjecture,
% 0.20/0.51      v1_funct_1(sK2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u99,negated_conjecture,
% 0.20/0.51      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 0.20/0.51  
% 0.20/0.51  cnf(u43,axiom,
% 0.20/0.51      m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u39,axiom,
% 0.20/0.51      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u104,negated_conjecture,
% 0.20/0.51      ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))).
% 0.20/0.51  
% 0.20/0.51  cnf(u52,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u53,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u54,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u42,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u45,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u50,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u51,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u96,negated_conjecture,
% 0.20/0.51      u1_struct_0(sK0) = k1_relat_1(sK2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u101,negated_conjecture,
% 0.20/0.51      k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u65,axiom,
% 0.20/0.51      k1_relset_1(X2,X3,sK3(X2,X3)) = k1_relat_1(sK3(X2,X3))).
% 0.20/0.51  
% 0.20/0.51  cnf(u63,axiom,
% 0.20/0.51      k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u80,axiom,
% 0.20/0.51      k1_relat_1(sK3(X3,X2)) != X3 | k1_xboole_0 = X2 | v1_funct_2(sK3(X3,X2),X3,X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u79,axiom,
% 0.20/0.51      k1_relat_1(k1_xboole_0) != X1 | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X1,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u73,axiom,
% 0.20/0.51      k1_xboole_0 != k1_relat_1(sK3(k1_xboole_0,X1)) | v1_funct_2(sK3(k1_xboole_0,X1),k1_xboole_0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u72,axiom,
% 0.20/0.51      k1_xboole_0 != k1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)).
% 0.20/0.51  
% 0.20/0.51  % (28427)# SZS output end Saturation.
% 0.20/0.51  % (28427)------------------------------
% 0.20/0.51  % (28427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28427)Termination reason: Satisfiable
% 0.20/0.51  
% 0.20/0.51  % (28427)Memory used [KB]: 1663
% 0.20/0.51  % (28427)Time elapsed: 0.095 s
% 0.20/0.51  % (28427)------------------------------
% 0.20/0.51  % (28427)------------------------------
% 0.20/0.51  % (28410)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (28409)Success in time 0.143 s
%------------------------------------------------------------------------------

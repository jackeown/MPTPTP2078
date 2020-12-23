%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:23 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of clauses        :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   50 (  50 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u29,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u27,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u31,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u48,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u47,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u28,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u26,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

% (19582)Refutation not found, incomplete strategy% (19582)------------------------------
% (19582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
cnf(u65,negated_conjecture,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

cnf(u23,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u66,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u70,negated_conjecture,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

cnf(u46,axiom,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0
    | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
    | ~ v1_funct_2(X2,k1_xboole_0,X1) )).

cnf(u43,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
    | v1_funct_2(X2,k1_xboole_0,X1) )).

cnf(u44,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | ~ v1_funct_2(X2,X0,k1_xboole_0) )).

cnf(u35,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1
    | k1_relset_1(X0,X1,X2) != X0
    | v1_funct_2(X2,X0,X1) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1
    | k1_relset_1(X0,X1,X2) = X0
    | ~ v1_funct_2(X2,X0,X1) )).

cnf(u32,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(X1) )).

cnf(u50,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u34,axiom,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) )).

cnf(u30,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u77,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(sK2)) )).

cnf(u33,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u67,negated_conjecture,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) )).

cnf(u63,negated_conjecture,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:21:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.42  % (19570)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.43  % (19580)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.43  % (19580)Refutation not found, incomplete strategy% (19580)------------------------------
% 0.19/0.43  % (19580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (19580)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.43  
% 0.19/0.43  % (19580)Memory used [KB]: 1663
% 0.19/0.43  % (19580)Time elapsed: 0.048 s
% 0.19/0.43  % (19580)------------------------------
% 0.19/0.43  % (19580)------------------------------
% 0.19/0.43  % (19570)Refutation not found, incomplete strategy% (19570)------------------------------
% 0.19/0.43  % (19570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (19570)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.43  
% 0.19/0.43  % (19570)Memory used [KB]: 10746
% 0.19/0.43  % (19570)Time elapsed: 0.050 s
% 0.19/0.43  % (19570)------------------------------
% 0.19/0.43  % (19570)------------------------------
% 0.19/0.45  % (19571)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.46  % (19568)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.47  % (19583)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.47  % (19573)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.47  % (19585)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.47  % (19569)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.47  % (19578)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.47  % (19585)Refutation not found, incomplete strategy% (19585)------------------------------
% 0.19/0.47  % (19585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (19585)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (19585)Memory used [KB]: 1663
% 0.19/0.47  % (19585)Time elapsed: 0.079 s
% 0.19/0.47  % (19585)------------------------------
% 0.19/0.47  % (19585)------------------------------
% 0.19/0.48  % (19575)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.48  % (19568)Refutation not found, incomplete strategy% (19568)------------------------------
% 0.19/0.48  % (19568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (19568)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (19568)Memory used [KB]: 10618
% 0.19/0.48  % (19568)Time elapsed: 0.082 s
% 0.19/0.48  % (19568)------------------------------
% 0.19/0.48  % (19568)------------------------------
% 0.19/0.48  % (19576)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.48  % (19586)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.19/0.48  % (19581)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.48  % (19583)Refutation not found, incomplete strategy% (19583)------------------------------
% 0.19/0.48  % (19583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (19583)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (19583)Memory used [KB]: 10746
% 0.19/0.48  % (19583)Time elapsed: 0.086 s
% 0.19/0.48  % (19583)------------------------------
% 0.19/0.48  % (19583)------------------------------
% 0.19/0.48  % (19574)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.48  % (19567)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.48  % (19586)Refutation not found, incomplete strategy% (19586)------------------------------
% 0.19/0.48  % (19586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (19586)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (19586)Memory used [KB]: 6140
% 0.19/0.48  % (19586)Time elapsed: 0.053 s
% 0.19/0.48  % (19586)------------------------------
% 0.19/0.48  % (19586)------------------------------
% 0.19/0.49  % (19567)Refutation not found, incomplete strategy% (19567)------------------------------
% 0.19/0.49  % (19567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (19567)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (19567)Memory used [KB]: 6140
% 0.19/0.49  % (19567)Time elapsed: 0.090 s
% 0.19/0.49  % (19567)------------------------------
% 0.19/0.49  % (19567)------------------------------
% 0.19/0.49  % (19577)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.49  % (19576)Refutation not found, incomplete strategy% (19576)------------------------------
% 0.19/0.49  % (19576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (19576)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (19576)Memory used [KB]: 10618
% 0.19/0.49  % (19576)Time elapsed: 0.066 s
% 0.19/0.49  % (19576)------------------------------
% 0.19/0.49  % (19576)------------------------------
% 0.19/0.49  % (19569)Refutation not found, incomplete strategy% (19569)------------------------------
% 0.19/0.49  % (19569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (19569)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (19569)Memory used [KB]: 10618
% 0.19/0.49  % (19569)Time elapsed: 0.090 s
% 0.19/0.49  % (19569)------------------------------
% 0.19/0.49  % (19569)------------------------------
% 0.19/0.49  % (19577)Refutation not found, incomplete strategy% (19577)------------------------------
% 0.19/0.49  % (19577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (19577)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (19577)Memory used [KB]: 6140
% 0.19/0.49  % (19573)Refutation not found, incomplete strategy% (19573)------------------------------
% 0.19/0.49  % (19573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (19573)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (19573)Memory used [KB]: 10746
% 0.19/0.49  % (19573)Time elapsed: 0.055 s
% 0.19/0.49  % (19573)------------------------------
% 0.19/0.49  % (19573)------------------------------
% 0.19/0.49  % (19577)Time elapsed: 0.097 s
% 0.19/0.49  % (19577)------------------------------
% 0.19/0.49  % (19577)------------------------------
% 0.19/0.49  % (19587)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.49  % (19578)Refutation not found, incomplete strategy% (19578)------------------------------
% 0.19/0.49  % (19578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (19578)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (19578)Memory used [KB]: 10618
% 0.19/0.49  % (19578)Time elapsed: 0.091 s
% 0.19/0.49  % (19578)------------------------------
% 0.19/0.49  % (19578)------------------------------
% 0.19/0.49  % (19587)Refutation not found, incomplete strategy% (19587)------------------------------
% 0.19/0.49  % (19587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (19587)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (19587)Memory used [KB]: 10618
% 0.19/0.49  % (19587)Time elapsed: 0.104 s
% 0.19/0.49  % (19587)------------------------------
% 0.19/0.49  % (19587)------------------------------
% 0.19/0.49  % (19584)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.19/0.49  % (19582)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.49  % (19572)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.19/0.49  % (19584)# SZS output start Saturation.
% 0.19/0.49  cnf(u29,negated_conjecture,
% 0.19/0.49      l1_orders_2(sK0)).
% 0.19/0.49  
% 0.19/0.49  cnf(u27,negated_conjecture,
% 0.19/0.49      l1_orders_2(sK1)).
% 0.19/0.49  
% 0.19/0.49  cnf(u31,axiom,
% 0.19/0.49      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.19/0.49  
% 0.19/0.49  cnf(u48,negated_conjecture,
% 0.19/0.49      l1_struct_0(sK0)).
% 0.19/0.49  
% 0.19/0.49  cnf(u47,negated_conjecture,
% 0.19/0.49      l1_struct_0(sK1)).
% 0.19/0.49  
% 0.19/0.49  cnf(u28,negated_conjecture,
% 0.19/0.49      ~v2_struct_0(sK0)).
% 0.19/0.49  
% 0.19/0.49  cnf(u26,negated_conjecture,
% 0.19/0.49      ~v2_struct_0(sK1)).
% 0.19/0.49  
% 0.19/0.49  % (19582)Refutation not found, incomplete strategy% (19582)------------------------------
% 0.19/0.49  % (19582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  cnf(u65,negated_conjecture,
% 0.19/0.49      v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))).
% 0.19/0.49  
% 0.19/0.49  cnf(u23,negated_conjecture,
% 0.19/0.49      v1_funct_1(sK2)).
% 0.19/0.49  
% 0.19/0.49  cnf(u66,negated_conjecture,
% 0.19/0.49      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 0.19/0.49  
% 0.19/0.49  cnf(u70,negated_conjecture,
% 0.19/0.49      ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))).
% 0.19/0.49  
% 0.19/0.49  cnf(u46,axiom,
% 0.19/0.49      ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)).
% 0.19/0.49  
% 0.19/0.49  cnf(u42,axiom,
% 0.19/0.49      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)).
% 0.19/0.49  
% 0.19/0.49  cnf(u43,axiom,
% 0.19/0.49      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)).
% 0.19/0.49  
% 0.19/0.49  cnf(u44,axiom,
% 0.19/0.49      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)).
% 0.19/0.49  
% 0.19/0.49  cnf(u35,axiom,
% 0.19/0.49      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)).
% 0.19/0.49  
% 0.19/0.49  cnf(u40,axiom,
% 0.19/0.49      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)).
% 0.19/0.49  
% 0.19/0.49  cnf(u41,axiom,
% 0.19/0.49      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)).
% 0.19/0.49  
% 0.19/0.49  cnf(u32,axiom,
% 0.19/0.49      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)).
% 0.19/0.49  
% 0.19/0.49  cnf(u50,negated_conjecture,
% 0.19/0.49      v1_relat_1(sK2)).
% 0.19/0.49  
% 0.19/0.49  cnf(u34,axiom,
% 0.19/0.49      v1_relat_1(k2_zfmisc_1(X0,X1))).
% 0.19/0.49  
% 0.19/0.49  cnf(u30,axiom,
% 0.19/0.49      v1_xboole_0(k1_xboole_0)).
% 0.19/0.49  
% 0.19/0.49  cnf(u77,negated_conjecture,
% 0.19/0.49      ~v1_xboole_0(k1_relat_1(sK2))).
% 0.19/0.49  
% 0.19/0.49  cnf(u33,axiom,
% 0.19/0.49      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.19/0.49  
% 0.19/0.49  cnf(u67,negated_conjecture,
% 0.19/0.49      k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)).
% 0.19/0.49  
% 0.19/0.49  cnf(u63,negated_conjecture,
% 0.19/0.49      u1_struct_0(sK0) = k1_relat_1(sK2)).
% 0.19/0.49  
% 0.19/0.49  % (19584)# SZS output end Saturation.
% 0.19/0.49  % (19584)------------------------------
% 0.19/0.49  % (19584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (19584)Termination reason: Satisfiable
% 0.19/0.49  
% 0.19/0.49  % (19584)Memory used [KB]: 1663
% 0.19/0.49  % (19584)Time elapsed: 0.097 s
% 0.19/0.49  % (19584)------------------------------
% 0.19/0.49  % (19584)------------------------------
% 0.19/0.49  % (19582)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (19582)Memory used [KB]: 6140
% 0.19/0.49  % (19582)Time elapsed: 0.107 s
% 0.19/0.49  % (19582)------------------------------
% 0.19/0.49  % (19582)------------------------------
% 0.19/0.50  % (19566)Success in time 0.154 s
%------------------------------------------------------------------------------

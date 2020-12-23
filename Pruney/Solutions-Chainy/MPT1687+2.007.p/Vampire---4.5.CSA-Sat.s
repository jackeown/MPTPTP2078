%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
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
cnf(u33,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u31,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u34,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u43,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u42,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u32,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u30,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u59,negated_conjecture,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | v1_xboole_0(u1_struct_0(sK1)) )).

cnf(u66,negated_conjecture,
    ( v1_partfun1(sK2,k1_relat_1(sK2)) )).

cnf(u38,axiom,
    ( ~ v1_partfun1(X1,X0)
    | ~ v4_relat_1(X1,X0)
    | k1_relat_1(X1) = X0
    | ~ v1_relat_1(X1) )).

cnf(u56,negated_conjecture,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

cnf(u71,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(sK2)) )).

cnf(u35,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u58,negated_conjecture,
    ( v4_relat_1(sK2,k1_relat_1(sK2)) )).

cnf(u41,axiom,
    ( ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | v1_partfun1(X1,k1_relat_1(X1)) )).

cnf(u57,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u61,negated_conjecture,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

cnf(u39,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(X2) )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v4_relat_1(X2,X0) )).

cnf(u36,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X0,X1)
    | v1_partfun1(X2,X0) )).

cnf(u27,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u44,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u54,negated_conjecture,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n012.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:21:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (22472)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.48  % (22464)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (22464)Refutation not found, incomplete strategy% (22464)------------------------------
% 0.22/0.48  % (22464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (22464)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (22464)Memory used [KB]: 10618
% 0.22/0.48  % (22464)Time elapsed: 0.071 s
% 0.22/0.48  % (22464)------------------------------
% 0.22/0.48  % (22464)------------------------------
% 0.22/0.49  % (22472)Refutation not found, incomplete strategy% (22472)------------------------------
% 0.22/0.49  % (22472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22472)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (22472)Memory used [KB]: 6140
% 0.22/0.49  % (22472)Time elapsed: 0.072 s
% 0.22/0.49  % (22472)------------------------------
% 0.22/0.49  % (22472)------------------------------
% 0.22/0.49  % (22466)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (22468)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (22477)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (22477)Refutation not found, incomplete strategy% (22477)------------------------------
% 0.22/0.49  % (22477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22477)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (22477)Memory used [KB]: 6140
% 0.22/0.49  % (22477)Time elapsed: 0.066 s
% 0.22/0.49  % (22477)------------------------------
% 0.22/0.49  % (22477)------------------------------
% 0.22/0.49  % (22468)Refutation not found, incomplete strategy% (22468)------------------------------
% 0.22/0.49  % (22468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22468)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (22468)Memory used [KB]: 10618
% 0.22/0.49  % (22468)Time elapsed: 0.080 s
% 0.22/0.49  % (22468)------------------------------
% 0.22/0.49  % (22468)------------------------------
% 0.22/0.50  % (22474)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (22474)Refutation not found, incomplete strategy% (22474)------------------------------
% 0.22/0.50  % (22474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22474)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (22474)Memory used [KB]: 6012
% 0.22/0.50  % (22474)Time elapsed: 0.002 s
% 0.22/0.50  % (22474)------------------------------
% 0.22/0.50  % (22474)------------------------------
% 0.22/0.50  % (22480)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (22480)Refutation not found, incomplete strategy% (22480)------------------------------
% 0.22/0.50  % (22480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22480)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (22480)Memory used [KB]: 1663
% 0.22/0.50  % (22480)Time elapsed: 0.078 s
% 0.22/0.50  % (22480)------------------------------
% 0.22/0.50  % (22480)------------------------------
% 0.22/0.50  % (22466)Refutation not found, incomplete strategy% (22466)------------------------------
% 0.22/0.50  % (22466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22466)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (22466)Memory used [KB]: 1663
% 0.22/0.50  % (22466)Time elapsed: 0.066 s
% 0.22/0.50  % (22466)------------------------------
% 0.22/0.50  % (22466)------------------------------
% 0.22/0.50  % (22478)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (22465)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (22475)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (22476)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (22463)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (22475)Refutation not found, incomplete strategy% (22475)------------------------------
% 0.22/0.50  % (22475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22475)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (22475)Memory used [KB]: 1663
% 0.22/0.50  % (22475)Time elapsed: 0.093 s
% 0.22/0.50  % (22475)------------------------------
% 0.22/0.50  % (22475)------------------------------
% 0.22/0.50  % (22467)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (22465)Refutation not found, incomplete strategy% (22465)------------------------------
% 0.22/0.50  % (22465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22465)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (22465)Memory used [KB]: 10746
% 0.22/0.50  % (22465)Time elapsed: 0.091 s
% 0.22/0.50  % (22465)------------------------------
% 0.22/0.50  % (22465)------------------------------
% 0.22/0.51  % (22463)Refutation not found, incomplete strategy% (22463)------------------------------
% 0.22/0.51  % (22463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22463)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22463)Memory used [KB]: 10618
% 0.22/0.51  % (22463)Time elapsed: 0.091 s
% 0.22/0.51  % (22463)------------------------------
% 0.22/0.51  % (22463)------------------------------
% 0.22/0.51  % (22470)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (22471)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (22473)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (22479)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (22462)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (22469)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (22473)Refutation not found, incomplete strategy% (22473)------------------------------
% 0.22/0.51  % (22473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22473)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22473)Memory used [KB]: 10618
% 0.22/0.51  % (22473)Time elapsed: 0.100 s
% 0.22/0.51  % (22473)------------------------------
% 0.22/0.51  % (22473)------------------------------
% 0.22/0.51  % (22482)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (22479)# SZS output start Saturation.
% 0.22/0.51  cnf(u33,negated_conjecture,
% 0.22/0.51      l1_orders_2(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u31,negated_conjecture,
% 0.22/0.51      l1_orders_2(sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u34,axiom,
% 0.22/0.51      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u43,negated_conjecture,
% 0.22/0.51      l1_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u42,negated_conjecture,
% 0.22/0.51      l1_struct_0(sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u32,negated_conjecture,
% 0.22/0.51      ~v2_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u30,negated_conjecture,
% 0.22/0.51      ~v2_struct_0(sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u59,negated_conjecture,
% 0.22/0.51      v1_partfun1(sK2,k1_relat_1(sK2)) | v1_xboole_0(u1_struct_0(sK1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u66,negated_conjecture,
% 0.22/0.51      v1_partfun1(sK2,k1_relat_1(sK2))).
% 0.22/0.51  
% 0.22/0.51  cnf(u38,axiom,
% 0.22/0.51      ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u56,negated_conjecture,
% 0.22/0.51      v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u71,negated_conjecture,
% 0.22/0.51      ~v1_xboole_0(k1_relat_1(sK2))).
% 0.22/0.51  
% 0.22/0.51  cnf(u35,axiom,
% 0.22/0.51      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u58,negated_conjecture,
% 0.22/0.51      v4_relat_1(sK2,k1_relat_1(sK2))).
% 0.22/0.51  
% 0.22/0.51  cnf(u41,axiom,
% 0.22/0.51      ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1) | v1_partfun1(X1,k1_relat_1(X1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u57,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 0.22/0.51  
% 0.22/0.51  cnf(u61,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))).
% 0.22/0.51  
% 0.22/0.51  cnf(u39,axiom,
% 0.22/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u40,axiom,
% 0.22/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u36,axiom,
% 0.22/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u27,negated_conjecture,
% 0.22/0.51      v1_funct_1(sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u44,negated_conjecture,
% 0.22/0.51      v1_relat_1(sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u54,negated_conjecture,
% 0.22/0.51      u1_struct_0(sK0) = k1_relat_1(sK2)).
% 0.22/0.51  
% 0.22/0.51  % (22479)# SZS output end Saturation.
% 0.22/0.51  % (22471)Refutation not found, incomplete strategy% (22471)------------------------------
% 0.22/0.51  % (22471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22471)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22471)Memory used [KB]: 10618
% 0.22/0.51  % (22471)Time elapsed: 0.102 s
% 0.22/0.51  % (22471)------------------------------
% 0.22/0.51  % (22471)------------------------------
% 0.22/0.51  % (22479)------------------------------
% 0.22/0.51  % (22479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22479)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (22479)Memory used [KB]: 1663
% 0.22/0.51  % (22479)Time elapsed: 0.106 s
% 0.22/0.51  % (22479)------------------------------
% 0.22/0.51  % (22479)------------------------------
% 0.22/0.51  % (22462)Refutation not found, incomplete strategy% (22462)------------------------------
% 0.22/0.51  % (22462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22462)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22462)Memory used [KB]: 6140
% 0.22/0.51  % (22462)Time elapsed: 0.100 s
% 0.22/0.51  % (22462)------------------------------
% 0.22/0.51  % (22462)------------------------------
% 0.22/0.51  % (22461)Success in time 0.153 s
%------------------------------------------------------------------------------

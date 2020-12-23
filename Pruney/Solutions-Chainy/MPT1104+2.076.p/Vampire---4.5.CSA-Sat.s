%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:00 EST 2020

% Result     : CounterSatisfiable 1.33s
% Output     : Saturation 1.33s
% Verified   : 
% Statistics : Number of clauses        :   43 (  43 expanded)
%              Number of leaves         :   43 (  43 expanded)
%              Depth                    :    0
%              Number of atoms          :   60 (  60 expanded)
%              Number of equality atoms :   37 (  37 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u18,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u32,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u44,negated_conjecture,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK2,X2) = k2_xboole_0(sK2,X2) )).

cnf(u45,negated_conjecture,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,X3) = k2_xboole_0(sK1,X3) )).

cnf(u30,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u31,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) )).

cnf(u43,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k2_xboole_0(X1,X0) = k4_subset_1(X1,X1,X0) )).

cnf(u33,negated_conjecture,
    ( r1_xboole_0(sK2,sK1) )).

cnf(u20,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u27,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) )).

cnf(u29,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 )).

cnf(u83,negated_conjecture,
    ( sK2 = k4_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u36,negated_conjecture,
    ( sK2 = k4_xboole_0(sK2,sK1) )).

cnf(u84,negated_conjecture,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u35,negated_conjecture,
    ( sK1 = k4_xboole_0(sK1,sK2) )).

cnf(u60,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

cnf(u61,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u19,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u42,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X3) = k4_xboole_0(sK1,X3) )).

cnf(u41,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X2) = k4_xboole_0(sK2,X2) )).

cnf(u57,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u59,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

cnf(u53,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k2_xboole_0(sK2,u1_struct_0(sK0)) )).

cnf(u54,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) )).

cnf(u23,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u40,axiom,
    ( k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u37,axiom,
    ( k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) )).

cnf(u26,axiom,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) )).

cnf(u80,negated_conjecture,
    ( k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

cnf(u79,negated_conjecture,
    ( k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) )).

cnf(u76,axiom,
    ( k2_xboole_0(X0,X0) = k4_subset_1(X0,X0,X0) )).

cnf(u25,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

cnf(u88,negated_conjecture,
    ( sK2 != k2_xboole_0(sK1,k2_struct_0(sK0))
    | r1_xboole_0(k2_xboole_0(sK1,k2_struct_0(sK0)),sK1) )).

cnf(u75,negated_conjecture,
    ( sK2 != k2_struct_0(sK0)
    | r1_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u21,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

cnf(u100,negated_conjecture,
    ( sK1 != k2_xboole_0(sK2,k2_struct_0(sK0))
    | r1_xboole_0(k2_xboole_0(sK2,k2_struct_0(sK0)),sK2) )).

cnf(u71,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | r1_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u69,axiom,
    ( k4_xboole_0(X3,X2) != k2_xboole_0(X2,k2_xboole_0(X2,X3))
    | r1_xboole_0(k2_xboole_0(X2,k2_xboole_0(X2,X3)),X2) )).

cnf(u67,axiom,
    ( k4_xboole_0(X0,X1) != k2_xboole_0(X1,k2_xboole_0(X0,X1))
    | r1_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X1)),X1) )).

cnf(u28,axiom,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) )).

cnf(u52,axiom,
    ( k2_xboole_0(X1,X2) != k4_xboole_0(X2,X1)
    | r1_xboole_0(k2_xboole_0(X1,X2),X1) )).

cnf(u39,axiom,
    ( k2_xboole_0(X0,X1) != k4_xboole_0(X0,X1)
    | r1_xboole_0(k2_xboole_0(X0,X1),X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:11:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (23981)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.47  % (23973)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (23973)Refutation not found, incomplete strategy% (23973)------------------------------
% 0.20/0.48  % (23973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23981)Refutation not found, incomplete strategy% (23981)------------------------------
% 0.20/0.48  % (23981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23973)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (23973)Memory used [KB]: 10618
% 0.20/0.48  % (23973)Time elapsed: 0.071 s
% 0.20/0.48  % (23973)------------------------------
% 0.20/0.48  % (23973)------------------------------
% 0.20/0.49  % (23981)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (23981)Memory used [KB]: 10746
% 0.20/0.49  % (23981)Time elapsed: 0.069 s
% 0.20/0.49  % (23981)------------------------------
% 0.20/0.49  % (23981)------------------------------
% 0.20/0.49  % (23975)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (23984)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (23984)Refutation not found, incomplete strategy% (23984)------------------------------
% 0.20/0.49  % (23984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (23984)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (23984)Memory used [KB]: 6012
% 0.20/0.49  % (23984)Time elapsed: 0.002 s
% 0.20/0.49  % (23984)------------------------------
% 0.20/0.49  % (23984)------------------------------
% 0.20/0.50  % (23972)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (23978)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.51  % (23991)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (23972)Refutation not found, incomplete strategy% (23972)------------------------------
% 0.20/0.51  % (23972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23972)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (23972)Memory used [KB]: 6140
% 0.20/0.51  % (23972)Time elapsed: 0.092 s
% 0.20/0.51  % (23972)------------------------------
% 0.20/0.51  % (23972)------------------------------
% 0.20/0.51  % (23976)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (23980)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.51  % (23982)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (23991)Refutation not found, incomplete strategy% (23991)------------------------------
% 0.20/0.51  % (23991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23991)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (23991)Memory used [KB]: 6140
% 0.20/0.51  % (23991)Time elapsed: 0.088 s
% 0.20/0.51  % (23991)------------------------------
% 0.20/0.51  % (23991)------------------------------
% 0.20/0.51  % (23978)Refutation not found, incomplete strategy% (23978)------------------------------
% 0.20/0.51  % (23978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23978)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (23978)Memory used [KB]: 10746
% 0.20/0.51  % (23978)Time elapsed: 0.094 s
% 0.20/0.51  % (23978)------------------------------
% 0.20/0.51  % (23978)------------------------------
% 0.20/0.51  % (23976)Refutation not found, incomplete strategy% (23976)------------------------------
% 0.20/0.51  % (23976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23976)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (23976)Memory used [KB]: 1663
% 0.20/0.51  % (23976)Time elapsed: 0.089 s
% 0.20/0.51  % (23976)------------------------------
% 0.20/0.51  % (23976)------------------------------
% 0.20/0.51  % (23982)Refutation not found, incomplete strategy% (23982)------------------------------
% 0.20/0.51  % (23982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23975)Refutation not found, incomplete strategy% (23975)------------------------------
% 0.20/0.51  % (23975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23975)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (23975)Memory used [KB]: 10618
% 0.20/0.51  % (23975)Time elapsed: 0.080 s
% 0.20/0.51  % (23975)------------------------------
% 0.20/0.51  % (23975)------------------------------
% 0.20/0.51  % (23982)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (23982)Memory used [KB]: 6140
% 0.20/0.51  % (23982)Time elapsed: 0.090 s
% 0.20/0.51  % (23982)------------------------------
% 0.20/0.51  % (23982)------------------------------
% 0.20/0.51  % (23977)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (23986)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.52  % (23987)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.52  % (23985)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.52  % (23990)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.52  % (23987)Refutation not found, incomplete strategy% (23987)------------------------------
% 0.20/0.52  % (23987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23987)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (23987)Memory used [KB]: 6140
% 0.20/0.52  % (23987)Time elapsed: 0.087 s
% 0.20/0.52  % (23987)------------------------------
% 0.20/0.52  % (23987)------------------------------
% 0.20/0.52  % (23988)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.52  % (23985)Refutation not found, incomplete strategy% (23985)------------------------------
% 0.20/0.52  % (23985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23985)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (23985)Memory used [KB]: 1663
% 0.20/0.52  % (23985)Time elapsed: 0.100 s
% 0.20/0.52  % (23985)------------------------------
% 0.20/0.52  % (23985)------------------------------
% 0.20/0.52  % (23974)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.52  % (23992)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.53  % (23979)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.53  % (23992)Refutation not found, incomplete strategy% (23992)------------------------------
% 0.20/0.53  % (23992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (23992)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (23992)Memory used [KB]: 10490
% 0.20/0.53  % (23992)Time elapsed: 0.107 s
% 0.20/0.53  % (23992)------------------------------
% 0.20/0.53  % (23992)------------------------------
% 0.20/0.53  % (23983)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.33/0.53  % (23983)Refutation not found, incomplete strategy% (23983)------------------------------
% 1.33/0.53  % (23983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (23983)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (23983)Memory used [KB]: 10618
% 1.33/0.53  % (23983)Time elapsed: 0.066 s
% 1.33/0.53  % (23983)------------------------------
% 1.33/0.53  % (23983)------------------------------
% 1.33/0.53  % (23989)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.33/0.53  % SZS status CounterSatisfiable for theBenchmark
% 1.33/0.53  % (23989)# SZS output start Saturation.
% 1.33/0.53  cnf(u22,negated_conjecture,
% 1.33/0.53      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.33/0.53  
% 1.33/0.53  cnf(u18,negated_conjecture,
% 1.33/0.53      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.33/0.53  
% 1.33/0.53  cnf(u32,axiom,
% 1.33/0.53      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.33/0.53  
% 1.33/0.53  cnf(u44,negated_conjecture,
% 1.33/0.53      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK2,X2) = k2_xboole_0(sK2,X2)).
% 1.33/0.53  
% 1.33/0.53  cnf(u45,negated_conjecture,
% 1.33/0.53      ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X3) = k2_xboole_0(sK1,X3)).
% 1.33/0.53  
% 1.33/0.53  cnf(u30,axiom,
% 1.33/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 1.33/0.53  
% 1.33/0.53  cnf(u31,axiom,
% 1.33/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)).
% 1.33/0.53  
% 1.33/0.53  cnf(u43,axiom,
% 1.33/0.53      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_xboole_0(X1,X0) = k4_subset_1(X1,X1,X0)).
% 1.33/0.53  
% 1.33/0.53  cnf(u33,negated_conjecture,
% 1.33/0.53      r1_xboole_0(sK2,sK1)).
% 1.33/0.53  
% 1.33/0.53  cnf(u20,negated_conjecture,
% 1.33/0.53      r1_xboole_0(sK1,sK2)).
% 1.33/0.53  
% 1.33/0.53  cnf(u27,axiom,
% 1.33/0.53      ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)).
% 1.33/0.53  
% 1.33/0.53  cnf(u29,axiom,
% 1.33/0.53      ~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0).
% 1.33/0.53  
% 1.33/0.53  cnf(u83,negated_conjecture,
% 1.33/0.53      sK2 = k4_xboole_0(k2_struct_0(sK0),sK1)).
% 1.33/0.53  
% 1.33/0.53  cnf(u36,negated_conjecture,
% 1.33/0.53      sK2 = k4_xboole_0(sK2,sK1)).
% 1.33/0.53  
% 1.33/0.53  cnf(u84,negated_conjecture,
% 1.33/0.53      sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)).
% 1.33/0.53  
% 1.33/0.53  cnf(u35,negated_conjecture,
% 1.33/0.53      sK1 = k4_xboole_0(sK1,sK2)).
% 1.33/0.53  
% 1.33/0.53  cnf(u60,negated_conjecture,
% 1.33/0.53      k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)).
% 1.33/0.53  
% 1.33/0.53  cnf(u61,negated_conjecture,
% 1.33/0.53      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 1.33/0.53  
% 1.33/0.53  cnf(u19,negated_conjecture,
% 1.33/0.53      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 1.33/0.53  
% 1.33/0.53  cnf(u42,negated_conjecture,
% 1.33/0.53      k7_subset_1(u1_struct_0(sK0),sK1,X3) = k4_xboole_0(sK1,X3)).
% 1.33/0.53  
% 1.33/0.53  cnf(u41,negated_conjecture,
% 1.33/0.53      k7_subset_1(u1_struct_0(sK0),sK2,X2) = k4_xboole_0(sK2,X2)).
% 1.33/0.53  
% 1.33/0.53  cnf(u57,negated_conjecture,
% 1.33/0.53      k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,u1_struct_0(sK0))).
% 1.33/0.53  
% 1.33/0.53  cnf(u59,negated_conjecture,
% 1.33/0.53      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)).
% 1.33/0.53  
% 1.33/0.53  cnf(u53,negated_conjecture,
% 1.33/0.53      k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k2_xboole_0(sK2,u1_struct_0(sK0))).
% 1.33/0.53  
% 1.33/0.53  cnf(u54,negated_conjecture,
% 1.33/0.53      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)).
% 1.33/0.54  
% 1.33/0.54  cnf(u23,axiom,
% 1.33/0.54      k2_subset_1(X0) = X0).
% 1.33/0.54  
% 1.33/0.54  cnf(u40,axiom,
% 1.33/0.54      k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u37,axiom,
% 1.33/0.54      k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u26,axiom,
% 1.33/0.54      k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u80,negated_conjecture,
% 1.33/0.54      k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u79,negated_conjecture,
% 1.33/0.54      k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)).
% 1.33/0.54  
% 1.33/0.54  cnf(u76,axiom,
% 1.33/0.54      k2_xboole_0(X0,X0) = k4_subset_1(X0,X0,X0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u25,axiom,
% 1.33/0.54      k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u88,negated_conjecture,
% 1.33/0.54      sK2 != k2_xboole_0(sK1,k2_struct_0(sK0)) | r1_xboole_0(k2_xboole_0(sK1,k2_struct_0(sK0)),sK1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u75,negated_conjecture,
% 1.33/0.54      sK2 != k2_struct_0(sK0) | r1_xboole_0(k2_struct_0(sK0),sK1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u21,negated_conjecture,
% 1.33/0.54      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u100,negated_conjecture,
% 1.33/0.54      sK1 != k2_xboole_0(sK2,k2_struct_0(sK0)) | r1_xboole_0(k2_xboole_0(sK2,k2_struct_0(sK0)),sK2)).
% 1.33/0.54  
% 1.33/0.54  cnf(u71,negated_conjecture,
% 1.33/0.54      sK1 != k2_struct_0(sK0) | r1_xboole_0(k2_struct_0(sK0),sK2)).
% 1.33/0.54  
% 1.33/0.54  cnf(u69,axiom,
% 1.33/0.54      k4_xboole_0(X3,X2) != k2_xboole_0(X2,k2_xboole_0(X2,X3)) | r1_xboole_0(k2_xboole_0(X2,k2_xboole_0(X2,X3)),X2)).
% 1.33/0.54  
% 1.33/0.54  cnf(u67,axiom,
% 1.33/0.54      k4_xboole_0(X0,X1) != k2_xboole_0(X1,k2_xboole_0(X0,X1)) | r1_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X1)),X1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u28,axiom,
% 1.33/0.54      k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u52,axiom,
% 1.33/0.54      k2_xboole_0(X1,X2) != k4_xboole_0(X2,X1) | r1_xboole_0(k2_xboole_0(X1,X2),X1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u39,axiom,
% 1.33/0.54      k2_xboole_0(X0,X1) != k4_xboole_0(X0,X1) | r1_xboole_0(k2_xboole_0(X0,X1),X1)).
% 1.33/0.54  
% 1.33/0.54  % (23989)# SZS output end Saturation.
% 1.33/0.54  % (23989)------------------------------
% 1.33/0.54  % (23989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (23989)Termination reason: Satisfiable
% 1.33/0.54  
% 1.33/0.54  % (23989)Memory used [KB]: 1663
% 1.33/0.54  % (23989)Time elapsed: 0.090 s
% 1.33/0.54  % (23989)------------------------------
% 1.33/0.54  % (23989)------------------------------
% 1.33/0.54  % (23971)Success in time 0.173 s
%------------------------------------------------------------------------------

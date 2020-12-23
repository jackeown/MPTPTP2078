%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:35 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   30 (  30 expanded)
%              Number of leaves         :   30 (  30 expanded)
%              Depth                    :    0
%              Number of atoms          :   37 (  37 expanded)
%              Number of equality atoms :   27 (  27 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u60,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u31,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u46,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u45,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u94,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u93,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u62,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u63,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u56,axiom,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 )).

cnf(u65,negated_conjecture,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u107,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

cnf(u97,axiom,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) )).

cnf(u92,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u96,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u118,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) )).

cnf(u102,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u124,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))) )).

cnf(u103,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

cnf(u29,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u73,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u84,axiom,
    ( k1_xboole_0 = k3_subset_1(X0,X0) )).

cnf(u38,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u115,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))))) )).

cnf(u95,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) )).

cnf(u82,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u72,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u85,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u54,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u51,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u59,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:13:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (3060)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.49  % (3073)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (3067)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (3060)Refutation not found, incomplete strategy% (3060)------------------------------
% 0.21/0.50  % (3060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3060)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (3060)Memory used [KB]: 1663
% 0.21/0.50  % (3060)Time elapsed: 0.093 s
% 0.21/0.50  % (3060)------------------------------
% 0.21/0.50  % (3060)------------------------------
% 0.21/0.50  % (3089)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.50  % (3075)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (3075)Refutation not found, incomplete strategy% (3075)------------------------------
% 0.21/0.50  % (3075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3075)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (3075)Memory used [KB]: 6140
% 0.21/0.50  % (3075)Time elapsed: 0.003 s
% 0.21/0.50  % (3075)------------------------------
% 0.21/0.50  % (3075)------------------------------
% 0.21/0.50  % (3065)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (3067)Refutation not found, incomplete strategy% (3067)------------------------------
% 0.21/0.51  % (3067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3067)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (3067)Memory used [KB]: 6268
% 0.21/0.51  % (3067)Time elapsed: 0.100 s
% 0.21/0.51  % (3067)------------------------------
% 0.21/0.51  % (3067)------------------------------
% 0.21/0.51  % (3064)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (3081)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (3082)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (3078)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (3082)Refutation not found, incomplete strategy% (3082)------------------------------
% 0.21/0.52  % (3082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3082)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (3082)Memory used [KB]: 10746
% 0.21/0.52  % (3082)Time elapsed: 0.086 s
% 0.21/0.52  % (3082)------------------------------
% 0.21/0.52  % (3082)------------------------------
% 0.21/0.52  % (3070)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (3084)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (3070)Refutation not found, incomplete strategy% (3070)------------------------------
% 0.21/0.53  % (3070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3070)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3070)Memory used [KB]: 10618
% 0.21/0.53  % (3070)Time elapsed: 0.134 s
% 0.21/0.53  % (3070)------------------------------
% 0.21/0.53  % (3070)------------------------------
% 0.21/0.53  % (3074)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (3063)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (3086)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (3088)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (3062)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (3065)Refutation not found, incomplete strategy% (3065)------------------------------
% 0.21/0.53  % (3065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3065)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3065)Memory used [KB]: 6268
% 0.21/0.53  % (3065)Time elapsed: 0.127 s
% 0.21/0.53  % (3065)------------------------------
% 0.21/0.53  % (3065)------------------------------
% 0.21/0.53  % (3083)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (3061)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (3083)Refutation not found, incomplete strategy% (3083)------------------------------
% 0.21/0.53  % (3083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3083)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3083)Memory used [KB]: 1791
% 0.21/0.53  % (3083)Time elapsed: 0.103 s
% 0.21/0.53  % (3083)------------------------------
% 0.21/0.53  % (3083)------------------------------
% 0.21/0.53  % (3087)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (3066)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.53  % (3066)# SZS output start Saturation.
% 0.21/0.53  cnf(u60,axiom,
% 0.21/0.53      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u31,negated_conjecture,
% 0.21/0.53      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.53  
% 0.21/0.53  cnf(u46,axiom,
% 0.21/0.53      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u45,axiom,
% 0.21/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.21/0.53  
% 0.21/0.53  cnf(u94,axiom,
% 0.21/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u93,axiom,
% 0.21/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u62,negated_conjecture,
% 0.21/0.53      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u63,axiom,
% 0.21/0.53      r1_tarski(X0,X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u56,axiom,
% 0.21/0.53      ~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u65,negated_conjecture,
% 0.21/0.53      sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))).
% 0.21/0.53  
% 0.21/0.53  cnf(u107,negated_conjecture,
% 0.21/0.53      k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u97,axiom,
% 0.21/0.53      k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u92,axiom,
% 0.21/0.53      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u96,negated_conjecture,
% 0.21/0.53      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u118,axiom,
% 0.21/0.53      k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2)))).
% 0.21/0.53  
% 0.21/0.53  cnf(u102,axiom,
% 0.21/0.53      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u124,negated_conjecture,
% 0.21/0.53      k1_xboole_0 = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)))).
% 0.21/0.53  
% 0.21/0.53  cnf(u103,negated_conjecture,
% 0.21/0.53      k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u29,negated_conjecture,
% 0.21/0.53      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u73,negated_conjecture,
% 0.21/0.53      sK1 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))).
% 0.21/0.53  
% 0.21/0.53  cnf(u84,axiom,
% 0.21/0.53      k1_xboole_0 = k3_subset_1(X0,X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u38,axiom,
% 0.21/0.53      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u115,negated_conjecture,
% 0.21/0.53      k1_xboole_0 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)))))).
% 0.21/0.53  
% 0.21/0.53  cnf(u95,axiom,
% 0.21/0.53      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))))).
% 0.21/0.53  
% 0.21/0.53  cnf(u82,axiom,
% 0.21/0.53      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u72,negated_conjecture,
% 0.21/0.53      k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u85,axiom,
% 0.21/0.53      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u54,axiom,
% 0.21/0.53      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u51,axiom,
% 0.21/0.53      k3_subset_1(X0,k1_xboole_0) = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u59,negated_conjecture,
% 0.21/0.53      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.53  
% 0.21/0.53  % (3066)# SZS output end Saturation.
% 0.21/0.53  % (3066)------------------------------
% 0.21/0.53  % (3066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3066)Termination reason: Satisfiable
% 0.21/0.53  
% 0.21/0.53  % (3066)Memory used [KB]: 6268
% 0.21/0.53  % (3066)Time elapsed: 0.103 s
% 0.21/0.53  % (3066)------------------------------
% 0.21/0.53  % (3066)------------------------------
% 0.21/0.54  % (3059)Success in time 0.179 s
%------------------------------------------------------------------------------

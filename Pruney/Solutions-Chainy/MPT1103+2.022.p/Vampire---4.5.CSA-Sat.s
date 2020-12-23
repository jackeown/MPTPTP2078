%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:37 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   49 (  49 expanded)
%              Number of leaves         :   49 (  49 expanded)
%              Depth                    :    0
%              Number of atoms          :   63 (  63 expanded)
%              Number of equality atoms :   48 (  48 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u70,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u38,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u35,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u190,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)) )).

cnf(u205,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0,sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),sK1) )).

cnf(u207,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | k3_subset_1(X4,k7_subset_1(X4,X3,X4)) = k4_subset_1(X4,k3_subset_1(X4,X3),X4) )).

cnf(u206,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k3_subset_1(X2,k7_subset_1(X2,X1,k1_xboole_0)) = k4_subset_1(X2,k3_subset_1(X2,X1),k1_xboole_0) )).

cnf(u194,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k4_subset_1(X2,X1,k1_xboole_0) = X1 )).

cnf(u192,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | k4_subset_1(X4,X3,X4) = k5_xboole_0(X3,k7_subset_1(X4,X4,X3)) )).

cnf(u83,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u82,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) )).

cnf(u53,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) )).

cnf(u52,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u204,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) )).

cnf(u202,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) )).

cnf(u195,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

cnf(u238,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

cnf(u73,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u236,negated_conjecture,
    ( u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

cnf(u235,negated_conjecture,
    ( u1_struct_0(sK0) = k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) )).

cnf(u230,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) )).

cnf(u234,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u233,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

cnf(u160,axiom,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k7_subset_1(X0,X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )).

cnf(u151,axiom,
    ( k1_setfam_1(k1_enumset1(X3,X3,k7_subset_1(X3,X3,X4))) = k7_subset_1(X3,X3,k1_setfam_1(k1_enumset1(X3,X3,X4))) )).

cnf(u135,axiom,
    ( k7_subset_1(X2,X2,k7_subset_1(X2,X2,X3)) = k1_setfam_1(k1_enumset1(X2,X2,X3)) )).

cnf(u64,axiom,
    ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 )).

cnf(u92,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u86,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u257,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) )).

cnf(u218,axiom,
    ( k4_subset_1(X0,k1_xboole_0,X0) = X0 )).

cnf(u220,axiom,
    ( k4_subset_1(X1,X1,X1) = X1 )).

cnf(u197,axiom,
    ( k4_subset_1(X1,X1,k1_xboole_0) = X1 )).

cnf(u247,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) )).

cnf(u60,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u110,axiom,
    ( k1_xboole_0 = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) )).

cnf(u61,axiom,
    ( k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) )).

cnf(u93,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

cnf(u81,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,k1_xboole_0,X2) )).

cnf(u33,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u196,axiom,
    ( k1_xboole_0 = k4_subset_1(X0,k1_xboole_0,k1_xboole_0) )).

cnf(u76,axiom,
    ( k1_xboole_0 = k3_subset_1(X0,X0) )).

cnf(u41,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u103,axiom,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 )).

cnf(u155,axiom,
    ( k5_xboole_0(X3,k7_subset_1(k7_subset_1(X3,X3,X4),k7_subset_1(X3,X3,X4),X3)) = k5_xboole_0(k7_subset_1(X3,X3,X4),k1_setfam_1(k1_enumset1(X3,X3,X4))) )).

cnf(u87,axiom,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) )).

cnf(u80,axiom,
    ( k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k1_enumset1(X3,X3,X4))) )).

cnf(u42,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u69,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:54:21 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.50  % (31347)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (31337)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (31339)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (31336)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (31346)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (31337)Refutation not found, incomplete strategy% (31337)------------------------------
% 0.21/0.52  % (31337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31333)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (31336)Refutation not found, incomplete strategy% (31336)------------------------------
% 0.21/0.53  % (31336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31336)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31336)Memory used [KB]: 10874
% 0.21/0.53  % (31336)Time elapsed: 0.108 s
% 0.21/0.53  % (31336)------------------------------
% 0.21/0.53  % (31336)------------------------------
% 0.21/0.53  % (31355)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (31337)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31337)Memory used [KB]: 6268
% 0.21/0.53  % (31337)Time elapsed: 0.107 s
% 0.21/0.53  % (31337)------------------------------
% 0.21/0.53  % (31337)------------------------------
% 0.21/0.53  % (31342)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (31363)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (31349)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (31355)Refutation not found, incomplete strategy% (31355)------------------------------
% 0.21/0.53  % (31355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31355)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31355)Memory used [KB]: 1791
% 0.21/0.53  % (31349)Refutation not found, incomplete strategy% (31349)------------------------------
% 0.21/0.53  % (31349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31349)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31349)Memory used [KB]: 6140
% 0.21/0.53  % (31349)Time elapsed: 0.002 s
% 0.21/0.53  % (31349)------------------------------
% 0.21/0.53  % (31349)------------------------------
% 0.21/0.53  % (31355)Time elapsed: 0.119 s
% 0.21/0.53  % (31355)------------------------------
% 0.21/0.53  % (31355)------------------------------
% 0.21/0.54  % (31341)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (31357)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (31339)# SZS output start Saturation.
% 0.21/0.54  cnf(u70,axiom,
% 0.21/0.54      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u38,axiom,
% 0.21/0.54      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u35,negated_conjecture,
% 0.21/0.54      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u190,negated_conjecture,
% 0.21/0.54      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u205,negated_conjecture,
% 0.21/0.54      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0,sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u207,axiom,
% 0.21/0.54      ~m1_subset_1(X3,k1_zfmisc_1(X4)) | k3_subset_1(X4,k7_subset_1(X4,X3,X4)) = k4_subset_1(X4,k3_subset_1(X4,X3),X4)).
% 0.21/0.54  
% 0.21/0.54  cnf(u206,axiom,
% 0.21/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | k3_subset_1(X2,k7_subset_1(X2,X1,k1_xboole_0)) = k4_subset_1(X2,k3_subset_1(X2,X1),k1_xboole_0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u194,axiom,
% 0.21/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | k4_subset_1(X2,X1,k1_xboole_0) = X1).
% 0.21/0.54  
% 0.21/0.54  cnf(u192,axiom,
% 0.21/0.54      ~m1_subset_1(X3,k1_zfmisc_1(X4)) | k4_subset_1(X4,X3,X4) = k5_xboole_0(X3,k7_subset_1(X4,X4,X3))).
% 0.21/0.54  
% 0.21/0.54  cnf(u83,axiom,
% 0.21/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u82,axiom,
% 0.21/0.54      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k7_subset_1(X2,X2,X1))).
% 0.21/0.54  
% 0.21/0.54  cnf(u53,axiom,
% 0.21/0.54      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u52,axiom,
% 0.21/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.21/0.54  
% 0.21/0.54  cnf(u204,negated_conjecture,
% 0.21/0.54      sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u202,negated_conjecture,
% 0.21/0.54      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u195,negated_conjecture,
% 0.21/0.54      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u238,negated_conjecture,
% 0.21/0.54      sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))).
% 0.21/0.54  
% 0.21/0.54  cnf(u73,negated_conjecture,
% 0.21/0.54      sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.21/0.54  
% 0.21/0.54  cnf(u236,negated_conjecture,
% 0.21/0.54      u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))).
% 0.21/0.54  
% 0.21/0.54  cnf(u235,negated_conjecture,
% 0.21/0.54      u1_struct_0(sK0) = k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u230,negated_conjecture,
% 0.21/0.54      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u234,negated_conjecture,
% 0.21/0.54      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u233,negated_conjecture,
% 0.21/0.54      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u160,axiom,
% 0.21/0.54      k1_setfam_1(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k7_subset_1(X0,X0,k1_setfam_1(k1_enumset1(X0,X0,X1))))).
% 0.21/0.54  
% 0.21/0.54  cnf(u151,axiom,
% 0.21/0.54      k1_setfam_1(k1_enumset1(X3,X3,k7_subset_1(X3,X3,X4))) = k7_subset_1(X3,X3,k1_setfam_1(k1_enumset1(X3,X3,X4)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u135,axiom,
% 0.21/0.54      k7_subset_1(X2,X2,k7_subset_1(X2,X2,X3)) = k1_setfam_1(k1_enumset1(X2,X2,X3))).
% 0.21/0.54  
% 0.21/0.54  cnf(u64,axiom,
% 0.21/0.54      k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u92,axiom,
% 0.21/0.54      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u86,negated_conjecture,
% 0.21/0.54      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u257,negated_conjecture,
% 0.21/0.54      k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u218,axiom,
% 0.21/0.54      k4_subset_1(X0,k1_xboole_0,X0) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u220,axiom,
% 0.21/0.54      k4_subset_1(X1,X1,X1) = X1).
% 0.21/0.54  
% 0.21/0.54  cnf(u197,axiom,
% 0.21/0.54      k4_subset_1(X1,X1,k1_xboole_0) = X1).
% 0.21/0.54  
% 0.21/0.54  cnf(u247,negated_conjecture,
% 0.21/0.54      k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u60,axiom,
% 0.21/0.54      k3_subset_1(X0,k1_xboole_0) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u110,axiom,
% 0.21/0.54      k1_xboole_0 = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u61,axiom,
% 0.21/0.54      k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u93,axiom,
% 0.21/0.54      k1_xboole_0 = k7_subset_1(X1,X1,X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u81,axiom,
% 0.21/0.54      k1_xboole_0 = k7_subset_1(X1,k1_xboole_0,X2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u33,negated_conjecture,
% 0.21/0.54      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u196,axiom,
% 0.21/0.54      k1_xboole_0 = k4_subset_1(X0,k1_xboole_0,k1_xboole_0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u76,axiom,
% 0.21/0.54      k1_xboole_0 = k3_subset_1(X0,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u41,axiom,
% 0.21/0.54      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u103,axiom,
% 0.21/0.54      k5_xboole_0(k1_xboole_0,X0) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u155,axiom,
% 0.21/0.54      k5_xboole_0(X3,k7_subset_1(k7_subset_1(X3,X3,X4),k7_subset_1(X3,X3,X4),X3)) = k5_xboole_0(k7_subset_1(X3,X3,X4),k1_setfam_1(k1_enumset1(X3,X3,X4)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u87,axiom,
% 0.21/0.54      k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1))).
% 0.21/0.54  
% 0.21/0.54  cnf(u80,axiom,
% 0.21/0.54      k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k1_enumset1(X3,X3,X4)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u42,axiom,
% 0.21/0.54      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u69,negated_conjecture,
% 0.21/0.54      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.54  
% 0.21/0.54  % (31339)# SZS output end Saturation.
% 0.21/0.54  % (31339)------------------------------
% 0.21/0.54  % (31339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31339)Termination reason: Satisfiable
% 0.21/0.54  
% 0.21/0.54  % (31339)Memory used [KB]: 6396
% 0.21/0.54  % (31339)Time elapsed: 0.116 s
% 0.21/0.54  % (31339)------------------------------
% 0.21/0.54  % (31339)------------------------------
% 0.21/0.54  % (31330)Success in time 0.172 s
%------------------------------------------------------------------------------

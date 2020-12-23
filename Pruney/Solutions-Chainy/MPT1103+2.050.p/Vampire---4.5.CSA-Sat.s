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
% DateTime   : Thu Dec  3 13:08:40 EST 2020

% Result     : CounterSatisfiable 1.72s
% Output     : Saturation 1.72s
% Verified   : 
% Statistics : Number of clauses        :   37 (  37 expanded)
%              Number of leaves         :   37 (  37 expanded)
%              Depth                    :    0
%              Number of atoms          :   50 (  50 expanded)
%              Number of equality atoms :   35 (  35 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u33,negated_conjecture,
    ( l1_struct_0(sK0) )).

% (29887)Refutation not found, incomplete strategy% (29887)------------------------------
% (29887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29887)Termination reason: Refutation not found, incomplete strategy

cnf(u44,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

% (29887)Memory used [KB]: 10746
cnf(u64,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

% (29887)Time elapsed: 0.172 s
% (29887)------------------------------
% (29887)------------------------------
cnf(u41,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u34,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u76,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u48,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )).

cnf(u55,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u60,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u53,axiom,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u51,axiom,
    ( ~ r1_tarski(X1,X0)
    | X0 = X1
    | ~ r1_tarski(X0,X1) )).

cnf(u82,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | k2_struct_0(sK0) = sK1 )).

cnf(u77,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u79,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u74,axiom,
    ( k7_subset_1(X1,k1_xboole_0,X2) = k4_xboole_0(k1_xboole_0,X2) )).

cnf(u73,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u63,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u40,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u59,axiom,
    ( k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) )).

cnf(u58,axiom,
    ( k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) )).

cnf(u57,axiom,
    ( k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) )).

cnf(u56,axiom,
    ( k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) )).

cnf(u54,axiom,
    ( k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) )).

cnf(u46,axiom,
    ( k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) )).

cnf(u45,axiom,
    ( k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) )).

cnf(u78,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) )).

cnf(u38,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) = sK1 )).

cnf(u72,axiom,
    ( k1_xboole_0 = k3_subset_1(X1,X1) )).

cnf(u39,axiom,
    ( k1_xboole_0 = k1_subset_1(X0) )).

cnf(u66,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u75,axiom,
    ( k7_subset_1(X3,X3,X4) = k4_xboole_0(X3,X4) )).

cnf(u68,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) )).

cnf(u47,axiom,
    ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

cnf(u71,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u52,axiom,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) )).

cnf(u83,axiom,
    ( k1_xboole_0 != X0
    | r1_tarski(X0,k1_xboole_0) )).

cnf(u35,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) != sK1 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:27:40 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.54  % (29868)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (29859)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (29868)Refutation not found, incomplete strategy% (29868)------------------------------
% 0.21/0.55  % (29868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (29860)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.56  % (29860)Refutation not found, incomplete strategy% (29860)------------------------------
% 0.21/0.56  % (29860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (29884)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.57  % (29860)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (29860)Memory used [KB]: 1663
% 0.21/0.57  % (29860)Time elapsed: 0.128 s
% 0.21/0.57  % (29860)------------------------------
% 0.21/0.57  % (29860)------------------------------
% 0.21/0.57  % (29861)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.57  % (29868)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (29868)Memory used [KB]: 1791
% 0.21/0.57  % (29868)Time elapsed: 0.125 s
% 0.21/0.57  % (29868)------------------------------
% 0.21/0.57  % (29868)------------------------------
% 0.21/0.57  % (29885)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (29884)Refutation not found, incomplete strategy% (29884)------------------------------
% 0.21/0.57  % (29884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (29884)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (29884)Memory used [KB]: 6268
% 0.21/0.57  % (29884)Time elapsed: 0.138 s
% 0.21/0.57  % (29884)------------------------------
% 0.21/0.57  % (29884)------------------------------
% 0.21/0.57  % (29874)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.57  % (29864)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.57  % (29877)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.57  % (29864)Refutation not found, incomplete strategy% (29864)------------------------------
% 0.21/0.57  % (29864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (29864)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (29864)Memory used [KB]: 1791
% 0.21/0.57  % (29864)Time elapsed: 0.144 s
% 0.21/0.57  % (29864)------------------------------
% 0.21/0.57  % (29864)------------------------------
% 0.21/0.58  % (29862)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.58  % (29877)Refutation not found, incomplete strategy% (29877)------------------------------
% 0.21/0.58  % (29877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (29885)Refutation not found, incomplete strategy% (29885)------------------------------
% 0.21/0.58  % (29885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (29882)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.58  % (29877)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (29877)Memory used [KB]: 1663
% 0.21/0.58  % (29877)Time elapsed: 0.152 s
% 0.21/0.58  % (29877)------------------------------
% 0.21/0.58  % (29877)------------------------------
% 0.21/0.58  % (29885)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (29885)Memory used [KB]: 6268
% 0.21/0.58  % (29885)Time elapsed: 0.150 s
% 0.21/0.58  % (29885)------------------------------
% 0.21/0.58  % (29885)------------------------------
% 0.21/0.59  % (29867)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.59  % (29869)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.59  % (29863)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.59  % (29869)Refutation not found, incomplete strategy% (29869)------------------------------
% 0.21/0.59  % (29869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (29869)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (29869)Memory used [KB]: 10746
% 0.21/0.59  % (29869)Time elapsed: 0.131 s
% 0.21/0.59  % (29869)------------------------------
% 0.21/0.59  % (29869)------------------------------
% 0.21/0.59  % (29888)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.59  % (29888)Refutation not found, incomplete strategy% (29888)------------------------------
% 0.21/0.59  % (29888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (29888)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (29888)Memory used [KB]: 1663
% 0.21/0.59  % (29888)Time elapsed: 0.001 s
% 0.21/0.59  % (29888)------------------------------
% 0.21/0.59  % (29888)------------------------------
% 0.21/0.59  % (29883)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.59  % (29883)Refutation not found, incomplete strategy% (29883)------------------------------
% 0.21/0.59  % (29883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (29883)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (29883)Memory used [KB]: 10618
% 0.21/0.59  % (29883)Time elapsed: 0.158 s
% 0.21/0.59  % (29883)------------------------------
% 0.21/0.59  % (29883)------------------------------
% 0.21/0.60  % (29886)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.60  % (29880)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.72/0.60  % (29886)Refutation not found, incomplete strategy% (29886)------------------------------
% 1.72/0.60  % (29886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.60  % (29886)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.60  
% 1.72/0.60  % (29886)Memory used [KB]: 6140
% 1.72/0.60  % (29886)Time elapsed: 0.171 s
% 1.72/0.60  % (29886)------------------------------
% 1.72/0.60  % (29886)------------------------------
% 1.72/0.60  % (29872)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.72/0.60  % (29866)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.72/0.60  % (29887)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.72/0.60  % SZS status CounterSatisfiable for theBenchmark
% 1.72/0.60  % (29866)# SZS output start Saturation.
% 1.72/0.60  cnf(u33,negated_conjecture,
% 1.72/0.60      l1_struct_0(sK0)).
% 1.72/0.60  
% 1.72/0.60  % (29887)Refutation not found, incomplete strategy% (29887)------------------------------
% 1.72/0.60  % (29887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.60  % (29887)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.60  
% 1.72/0.60  cnf(u44,axiom,
% 1.72/0.60      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 1.72/0.60  
% 1.72/0.60  % (29887)Memory used [KB]: 10746
% 1.72/0.60  cnf(u64,axiom,
% 1.72/0.60      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.72/0.60  
% 1.72/0.60  % (29887)Time elapsed: 0.172 s
% 1.72/0.60  % (29887)------------------------------
% 1.72/0.60  % (29887)------------------------------
% 1.72/0.60  cnf(u41,axiom,
% 1.72/0.60      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 1.72/0.60  
% 1.72/0.60  cnf(u34,negated_conjecture,
% 1.72/0.60      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.72/0.60  
% 1.72/0.60  cnf(u76,negated_conjecture,
% 1.72/0.60      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 1.72/0.60  
% 1.72/0.60  cnf(u48,axiom,
% 1.72/0.60      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)).
% 1.72/0.60  
% 1.72/0.60  cnf(u55,axiom,
% 1.72/0.60      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 1.72/0.60  
% 1.72/0.60  cnf(u60,axiom,
% 1.72/0.60      r1_tarski(X1,X1)).
% 1.72/0.60  
% 1.72/0.60  cnf(u53,axiom,
% 1.72/0.60      ~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0).
% 1.72/0.60  
% 1.72/0.60  cnf(u51,axiom,
% 1.72/0.60      ~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)).
% 1.72/0.60  
% 1.72/0.60  cnf(u82,negated_conjecture,
% 1.72/0.60      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | k2_struct_0(sK0) = sK1).
% 1.72/0.60  
% 1.72/0.60  cnf(u77,negated_conjecture,
% 1.72/0.60      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 1.72/0.60  
% 1.72/0.60  cnf(u79,negated_conjecture,
% 1.72/0.60      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 1.72/0.60  
% 1.72/0.60  cnf(u74,axiom,
% 1.72/0.60      k7_subset_1(X1,k1_xboole_0,X2) = k4_xboole_0(k1_xboole_0,X2)).
% 1.72/0.60  
% 1.72/0.60  cnf(u73,negated_conjecture,
% 1.72/0.60      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 1.72/0.60  
% 1.72/0.60  cnf(u63,axiom,
% 1.72/0.60      k3_subset_1(X0,k1_xboole_0) = X0).
% 1.72/0.60  
% 1.72/0.60  cnf(u40,axiom,
% 1.72/0.60      k2_subset_1(X0) = X0).
% 1.72/0.60  
% 1.72/0.60  cnf(u59,axiom,
% 1.72/0.60      k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)).
% 1.72/0.60  
% 1.72/0.60  cnf(u58,axiom,
% 1.72/0.60      k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)).
% 1.72/0.60  
% 1.72/0.60  cnf(u57,axiom,
% 1.72/0.60      k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)).
% 1.72/0.60  
% 1.72/0.60  cnf(u56,axiom,
% 1.72/0.60      k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)).
% 1.72/0.60  
% 1.72/0.60  cnf(u54,axiom,
% 1.72/0.60      k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)).
% 1.72/0.60  
% 1.72/0.60  cnf(u46,axiom,
% 1.72/0.60      k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)).
% 1.72/0.60  
% 1.72/0.60  cnf(u45,axiom,
% 1.72/0.60      k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))).
% 1.72/0.60  
% 1.72/0.60  cnf(u78,negated_conjecture,
% 1.72/0.60      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))).
% 1.72/0.60  
% 1.72/0.60  cnf(u38,negated_conjecture,
% 1.72/0.60      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) = sK1).
% 1.72/0.60  
% 1.72/0.60  cnf(u72,axiom,
% 1.72/0.60      k1_xboole_0 = k3_subset_1(X1,X1)).
% 1.72/0.60  
% 1.72/0.60  cnf(u39,axiom,
% 1.72/0.60      k1_xboole_0 = k1_subset_1(X0)).
% 1.72/0.60  
% 1.72/0.60  cnf(u66,axiom,
% 1.72/0.60      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 1.72/0.60  
% 1.72/0.60  cnf(u75,axiom,
% 1.72/0.60      k7_subset_1(X3,X3,X4) = k4_xboole_0(X3,X4)).
% 1.72/0.60  
% 1.72/0.60  cnf(u68,negated_conjecture,
% 1.72/0.60      k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1)).
% 1.72/0.60  
% 1.72/0.60  cnf(u47,axiom,
% 1.72/0.60      k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))).
% 1.72/0.60  
% 1.72/0.60  cnf(u71,axiom,
% 1.72/0.60      k4_xboole_0(X0,k1_xboole_0) = X0).
% 1.72/0.60  
% 1.72/0.60  cnf(u52,axiom,
% 1.72/0.60      k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)).
% 1.72/0.60  
% 1.72/0.60  cnf(u83,axiom,
% 1.72/0.60      k1_xboole_0 != X0 | r1_tarski(X0,k1_xboole_0)).
% 1.72/0.60  
% 1.72/0.60  cnf(u35,negated_conjecture,
% 1.72/0.60      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) != sK1).
% 1.72/0.60  
% 1.72/0.60  % (29866)# SZS output end Saturation.
% 1.72/0.60  % (29866)------------------------------
% 1.72/0.60  % (29866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.60  % (29866)Termination reason: Satisfiable
% 1.72/0.60  
% 1.72/0.60  % (29866)Memory used [KB]: 1791
% 1.72/0.60  % (29866)Time elapsed: 0.125 s
% 1.72/0.60  % (29866)------------------------------
% 1.72/0.60  % (29866)------------------------------
% 1.72/0.60  % (29858)Success in time 0.239 s
%------------------------------------------------------------------------------

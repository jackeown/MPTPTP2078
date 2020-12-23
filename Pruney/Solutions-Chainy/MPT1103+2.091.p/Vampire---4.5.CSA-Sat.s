%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:46 EST 2020

% Result     : CounterSatisfiable 1.40s
% Output     : Saturation 1.40s
% Verified   : 
% Statistics : Number of clauses        :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   36 (  36 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u43,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u25,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u52,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u44,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u45,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u33,axiom,
    ( ~ r1_tarski(X0,X1)
    | X0 = X1
    | r2_xboole_0(X0,X1) )).

cnf(u47,negated_conjecture,
    ( r2_xboole_0(sK1,u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) )).

% (24815)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
cnf(u80,axiom,
    ( ~ r2_xboole_0(k7_subset_1(X2,X2,X3),X2)
    | k1_xboole_0 != k1_setfam_1(k2_tarski(X2,X3)) )).

cnf(u70,axiom,
    ( ~ r2_xboole_0(X1,X1) )).

cnf(u49,axiom,
    ( ~ r2_xboole_0(k1_xboole_0,X0)
    | k1_xboole_0 != X0 )).

cnf(u38,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

cnf(u78,axiom,
    ( k1_setfam_1(k2_tarski(X2,k7_subset_1(X2,X2,X3))) = k7_subset_1(X2,X2,k1_setfam_1(k2_tarski(X2,X3))) )).

cnf(u62,axiom,
    ( k7_subset_1(X2,X2,k7_subset_1(X2,X2,X3)) = k1_setfam_1(k2_tarski(X2,X3)) )).

cnf(u55,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u66,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u23,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u51,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u83,axiom,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k7_subset_1(X0,X0,k1_setfam_1(k2_tarski(X0,X1)))) )).

cnf(u73,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u72,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u57,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u26,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u28,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u53,axiom,
    ( k1_xboole_0 != k7_subset_1(X1,X1,X0)
    | ~ r2_xboole_0(X0,X1) )).

cnf(u42,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:00:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.26/0.53  % (24811)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.26/0.53  % (24806)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.26/0.53  % (24813)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.26/0.53  % (24809)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.26/0.53  % (24829)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.26/0.54  % (24808)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.26/0.54  % (24813)Refutation not found, incomplete strategy% (24813)------------------------------
% 1.26/0.54  % (24813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (24808)Refutation not found, incomplete strategy% (24808)------------------------------
% 1.26/0.54  % (24808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (24808)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.54  
% 1.26/0.54  % (24808)Memory used [KB]: 6268
% 1.26/0.54  % (24808)Time elapsed: 0.127 s
% 1.26/0.54  % (24808)------------------------------
% 1.26/0.54  % (24808)------------------------------
% 1.26/0.54  % (24813)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.54  
% 1.26/0.54  % (24813)Memory used [KB]: 10618
% 1.26/0.54  % (24813)Time elapsed: 0.118 s
% 1.26/0.54  % (24813)------------------------------
% 1.26/0.54  % (24813)------------------------------
% 1.40/0.54  % (24821)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.55  % (24821)Refutation not found, incomplete strategy% (24821)------------------------------
% 1.40/0.55  % (24821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (24804)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.40/0.55  % (24824)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.55  % (24833)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.40/0.55  % (24819)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.40/0.55  % (24831)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.55  % (24820)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.55  % (24811)Refutation not found, incomplete strategy% (24811)------------------------------
% 1.40/0.55  % (24811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (24811)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (24811)Memory used [KB]: 6268
% 1.40/0.55  % (24811)Time elapsed: 0.133 s
% 1.40/0.55  % (24811)------------------------------
% 1.40/0.55  % (24811)------------------------------
% 1.40/0.55  % (24821)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (24821)Memory used [KB]: 10618
% 1.40/0.55  % (24821)Time elapsed: 0.119 s
% 1.40/0.55  % (24821)------------------------------
% 1.40/0.55  % (24821)------------------------------
% 1.40/0.55  % (24816)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.55  % (24804)Refutation not found, incomplete strategy% (24804)------------------------------
% 1.40/0.55  % (24804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (24804)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (24804)Memory used [KB]: 1663
% 1.40/0.55  % (24804)Time elapsed: 0.133 s
% 1.40/0.55  % (24804)------------------------------
% 1.40/0.55  % (24804)------------------------------
% 1.40/0.55  % (24830)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.55  % (24825)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.40/0.56  % (24827)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.56  % (24816)Refutation not found, incomplete strategy% (24816)------------------------------
% 1.40/0.56  % (24816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (24825)Refutation not found, incomplete strategy% (24825)------------------------------
% 1.40/0.56  % (24825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (24825)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (24825)Memory used [KB]: 1791
% 1.40/0.56  % (24825)Time elapsed: 0.138 s
% 1.40/0.56  % (24825)------------------------------
% 1.40/0.56  % (24825)------------------------------
% 1.40/0.56  % (24812)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.56  % (24827)Refutation not found, incomplete strategy% (24827)------------------------------
% 1.40/0.56  % (24827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (24827)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (24827)Memory used [KB]: 1663
% 1.40/0.56  % (24827)Time elapsed: 0.139 s
% 1.40/0.56  % (24827)------------------------------
% 1.40/0.56  % (24827)------------------------------
% 1.40/0.56  % (24805)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.40/0.56  % (24807)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.40/0.56  % (24816)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (24816)Memory used [KB]: 6268
% 1.40/0.56  % (24816)Time elapsed: 0.144 s
% 1.40/0.56  % (24816)------------------------------
% 1.40/0.56  % (24816)------------------------------
% 1.40/0.56  % (24812)Refutation not found, incomplete strategy% (24812)------------------------------
% 1.40/0.56  % (24812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (24812)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (24812)Memory used [KB]: 10746
% 1.40/0.56  % (24812)Time elapsed: 0.139 s
% 1.40/0.56  % (24812)------------------------------
% 1.40/0.56  % (24812)------------------------------
% 1.40/0.56  % (24824)Refutation not found, incomplete strategy% (24824)------------------------------
% 1.40/0.56  % (24824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (24817)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.40/0.56  % (24824)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (24824)Memory used [KB]: 10746
% 1.40/0.56  % (24824)Time elapsed: 0.149 s
% 1.40/0.56  % (24824)------------------------------
% 1.40/0.56  % (24824)------------------------------
% 1.40/0.56  % (24814)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.40/0.56  % (24828)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.56  % (24814)Refutation not found, incomplete strategy% (24814)------------------------------
% 1.40/0.56  % (24814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (24814)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (24814)Memory used [KB]: 10618
% 1.40/0.56  % (24814)Time elapsed: 0.149 s
% 1.40/0.56  % (24814)------------------------------
% 1.40/0.56  % (24814)------------------------------
% 1.40/0.56  % (24822)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.56  % (24823)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.56  % (24826)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.40/0.56  % (24818)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.40/0.56  % (24819)Refutation not found, incomplete strategy% (24819)------------------------------
% 1.40/0.56  % (24819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (24819)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (24819)Memory used [KB]: 6140
% 1.40/0.56  % (24819)Time elapsed: 0.150 s
% 1.40/0.56  % (24819)------------------------------
% 1.40/0.56  % (24819)------------------------------
% 1.40/0.57  % (24810)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.40/0.57  % (24832)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.58  % SZS status CounterSatisfiable for theBenchmark
% 1.40/0.58  % (24810)# SZS output start Saturation.
% 1.40/0.58  cnf(u43,axiom,
% 1.40/0.58      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.40/0.58  
% 1.40/0.58  cnf(u25,negated_conjecture,
% 1.40/0.58      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.40/0.58  
% 1.40/0.58  cnf(u34,axiom,
% 1.40/0.58      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 1.40/0.58  
% 1.40/0.58  cnf(u52,axiom,
% 1.40/0.58      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.40/0.58  
% 1.40/0.58  cnf(u44,negated_conjecture,
% 1.40/0.58      r1_tarski(sK1,u1_struct_0(sK0))).
% 1.40/0.58  
% 1.40/0.58  cnf(u45,axiom,
% 1.40/0.58      r1_tarski(X0,X0)).
% 1.40/0.58  
% 1.40/0.58  cnf(u33,axiom,
% 1.40/0.58      ~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)).
% 1.40/0.58  
% 1.40/0.58  cnf(u47,negated_conjecture,
% 1.40/0.58      r2_xboole_0(sK1,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)).
% 1.40/0.58  
% 1.40/0.58  % (24815)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.40/0.58  cnf(u80,axiom,
% 1.40/0.58      ~r2_xboole_0(k7_subset_1(X2,X2,X3),X2) | k1_xboole_0 != k1_setfam_1(k2_tarski(X2,X3))).
% 1.40/0.58  
% 1.40/0.58  cnf(u70,axiom,
% 1.40/0.58      ~r2_xboole_0(X1,X1)).
% 1.40/0.58  
% 1.40/0.58  cnf(u49,axiom,
% 1.40/0.58      ~r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 != X0).
% 1.40/0.58  
% 1.40/0.58  cnf(u38,axiom,
% 1.40/0.58      k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))).
% 1.40/0.58  
% 1.40/0.58  cnf(u78,axiom,
% 1.40/0.58      k1_setfam_1(k2_tarski(X2,k7_subset_1(X2,X2,X3))) = k7_subset_1(X2,X2,k1_setfam_1(k2_tarski(X2,X3)))).
% 1.40/0.58  
% 1.40/0.58  cnf(u62,axiom,
% 1.40/0.58      k7_subset_1(X2,X2,k7_subset_1(X2,X2,X3)) = k1_setfam_1(k2_tarski(X2,X3))).
% 1.40/0.58  
% 1.40/0.58  cnf(u55,negated_conjecture,
% 1.40/0.58      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 1.40/0.58  
% 1.40/0.58  cnf(u66,axiom,
% 1.40/0.58      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 1.40/0.58  
% 1.40/0.58  cnf(u23,negated_conjecture,
% 1.40/0.58      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 1.40/0.58  
% 1.40/0.58  cnf(u51,axiom,
% 1.40/0.58      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 1.40/0.58  
% 1.40/0.58  cnf(u83,axiom,
% 1.40/0.58      k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k7_subset_1(X0,X0,k1_setfam_1(k2_tarski(X0,X1))))).
% 1.40/0.58  
% 1.40/0.58  cnf(u73,axiom,
% 1.40/0.58      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 1.40/0.58  
% 1.40/0.58  cnf(u72,axiom,
% 1.40/0.58      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 1.40/0.58  
% 1.40/0.58  cnf(u57,axiom,
% 1.40/0.58      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 1.40/0.58  
% 1.40/0.58  cnf(u26,axiom,
% 1.40/0.58      k2_subset_1(X0) = X0).
% 1.40/0.58  
% 1.40/0.58  cnf(u28,axiom,
% 1.40/0.58      k5_xboole_0(X0,k1_xboole_0) = X0).
% 1.40/0.58  
% 1.40/0.58  cnf(u53,axiom,
% 1.40/0.58      k1_xboole_0 != k7_subset_1(X1,X1,X0) | ~r2_xboole_0(X0,X1)).
% 1.40/0.58  
% 1.40/0.58  cnf(u42,negated_conjecture,
% 1.40/0.58      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.40/0.58  
% 1.40/0.58  % (24810)# SZS output end Saturation.
% 1.40/0.58  % (24810)------------------------------
% 1.40/0.58  % (24810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.58  % (24810)Termination reason: Satisfiable
% 1.40/0.58  
% 1.40/0.58  % (24810)Memory used [KB]: 6268
% 1.40/0.58  % (24810)Time elapsed: 0.071 s
% 1.40/0.58  % (24810)------------------------------
% 1.40/0.58  % (24810)------------------------------
% 1.40/0.58  % (24815)Refutation not found, incomplete strategy% (24815)------------------------------
% 1.40/0.58  % (24815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.58  % (24815)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.58  
% 1.40/0.58  % (24815)Memory used [KB]: 10618
% 1.40/0.58  % (24815)Time elapsed: 0.156 s
% 1.40/0.58  % (24815)------------------------------
% 1.40/0.58  % (24815)------------------------------
% 1.40/0.58  % (24830)Refutation not found, incomplete strategy% (24830)------------------------------
% 1.40/0.58  % (24830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.58  % (24830)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.58  
% 1.40/0.58  % (24830)Memory used [KB]: 10746
% 1.40/0.58  % (24830)Time elapsed: 0.168 s
% 1.40/0.58  % (24830)------------------------------
% 1.40/0.58  % (24830)------------------------------
% 1.40/0.58  % (24801)Success in time 0.208 s
%------------------------------------------------------------------------------

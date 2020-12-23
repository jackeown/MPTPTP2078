%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:58 EST 2020

% Result     : CounterSatisfiable 1.60s
% Output     : Saturation 1.60s
% Verified   : 
% Statistics : Number of clauses        :   71 (  71 expanded)
%              Number of leaves         :   71 (  71 expanded)
%              Depth                    :    0
%              Number of atoms          :   80 (  80 expanded)
%              Number of equality atoms :   55 (  55 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u58,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u32,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u241,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2)) )).

cnf(u242,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k3_tarski(k2_tarski(X1,sK1)) )).

cnf(u47,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u56,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) )).

cnf(u243,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | k3_tarski(k2_tarski(X2,X3)) = k4_subset_1(X3,X2,X3) )).

cnf(u275,negated_conjecture,
    ( r1_tarski(sK2,k2_struct_0(sK0)) )).

cnf(u253,negated_conjecture,
    ( r1_tarski(sK1,k2_struct_0(sK0)) )).

cnf(u785,axiom,
    ( r1_tarski(X0,k4_subset_1(X0,X0,X0)) )).

cnf(u134,axiom,
    ( r1_tarski(X8,k3_tarski(k2_tarski(X9,X8))) )).

cnf(u133,axiom,
    ( r1_tarski(X6,k3_tarski(k2_tarski(X6,X7))) )).

cnf(u370,axiom,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) )).

cnf(u105,axiom,
    ( r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4) )).

cnf(u60,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u59,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u37,axiom,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) )).

cnf(u54,axiom,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 )).

cnf(u61,negated_conjecture,
    ( r1_xboole_0(sK2,sK1) )).

cnf(u30,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u45,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) )).

cnf(u55,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0 )).

cnf(u240,axiom,
    ( k4_xboole_0(X2,X3) = k7_subset_1(X2,X2,X3) )).

cnf(u781,negated_conjecture,
    ( k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u780,negated_conjecture,
    ( k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u782,axiom,
    ( k3_tarski(k2_tarski(X0,X0)) = k4_subset_1(X0,X0,X0) )).

cnf(u784,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) )).

cnf(u783,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2) )).

cnf(u336,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u29,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u337,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) )).

% (12628)Refutation not found, incomplete strategy% (12628)------------------------------
% (12628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
cnf(u252,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) )).

% (12628)Termination reason: Refutation not found, incomplete strategy

% (12628)Memory used [KB]: 6780
% (12628)Time elapsed: 0.154 s
% (12628)------------------------------
% (12628)------------------------------
cnf(u247,negated_conjecture,
    ( k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)) )).

cnf(u52,axiom,
    ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) )).

cnf(u248,negated_conjecture,
    ( sK2 = k5_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u249,negated_conjecture,
    ( sK1 = k5_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u805,axiom,
    ( k4_xboole_0(k4_subset_1(X4,X4,X4),X4) = k5_xboole_0(k4_subset_1(X4,X4,X4),X4) )).

cnf(u185,axiom,
    ( k4_xboole_0(k3_tarski(k2_tarski(X9,X8)),X8) = k5_xboole_0(k3_tarski(k2_tarski(X9,X8)),X8) )).

cnf(u184,axiom,
    ( k4_xboole_0(k3_tarski(k2_tarski(X6,X7)),X6) = k5_xboole_0(k3_tarski(k2_tarski(X6,X7)),X6) )).

cnf(u1418,axiom,
    ( k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X24)),k1_xboole_0) = k5_xboole_0(k4_xboole_0(X24,k4_xboole_0(X24,X23)),k1_xboole_0) )).

cnf(u973,axiom,
    ( k4_xboole_0(X29,k4_xboole_0(X29,X30)) = k5_xboole_0(k4_xboole_0(X30,k4_xboole_0(X30,X29)),k1_xboole_0) )).

cnf(u775,axiom,
    ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(X20,k4_xboole_0(X20,X19)),k4_xboole_0(X19,k4_xboole_0(X19,X20))) )).

cnf(u465,axiom,
    ( k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3)) )).

cnf(u78,axiom,
    ( k1_xboole_0 = k5_xboole_0(X1,X1) )).

cnf(u354,axiom,
    ( k4_xboole_0(X2,k4_xboole_0(X2,X3)) = k5_xboole_0(X2,k4_xboole_0(X2,X3)) )).

cnf(u103,axiom,
    ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) )).

cnf(u49,axiom,
    ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) )).

cnf(u250,negated_conjecture,
    ( sK2 = k4_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u251,negated_conjecture,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u239,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1) )).

cnf(u238,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) )).

cnf(u265,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK2,k2_struct_0(sK0)) )).

cnf(u287,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0)) )).

cnf(u89,axiom,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) )).

cnf(u762,axiom,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10))) )).

cnf(u386,axiom,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) )).

cnf(u371,axiom,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,X11),X10) )).

cnf(u787,axiom,
    ( k1_xboole_0 = k4_xboole_0(X2,k4_subset_1(X2,X2,X2)) )).

cnf(u64,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_tarski(X1,X0))) )).

cnf(u51,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) )).

cnf(u57,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u958,axiom,
    ( k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X5)),k1_xboole_0) )).

cnf(u971,axiom,
    ( k4_xboole_0(X27,k4_xboole_0(X27,X28)) = k4_xboole_0(k4_xboole_0(X28,k4_xboole_0(X28,X27)),k1_xboole_0) )).

cnf(u459,axiom,
    ( k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k4_xboole_0(X10,X9) )).

cnf(u351,axiom,
    ( k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) )).

cnf(u53,axiom,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) )).

cnf(u77,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u35,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u33,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u31,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:13:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (12624)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (12618)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (12644)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (12642)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (12630)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (12631)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (12626)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (12642)Refutation not found, incomplete strategy% (12642)------------------------------
% 0.21/0.53  % (12642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12644)Refutation not found, incomplete strategy% (12644)------------------------------
% 0.21/0.53  % (12644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12644)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12644)Memory used [KB]: 10874
% 0.21/0.53  % (12644)Time elapsed: 0.060 s
% 0.21/0.53  % (12644)------------------------------
% 0.21/0.53  % (12644)------------------------------
% 0.21/0.53  % (12633)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (12642)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12642)Memory used [KB]: 10874
% 0.21/0.53  % (12642)Time elapsed: 0.063 s
% 0.21/0.53  % (12642)------------------------------
% 0.21/0.53  % (12642)------------------------------
% 0.21/0.53  % (12635)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (12624)Refutation not found, incomplete strategy% (12624)------------------------------
% 0.21/0.54  % (12624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12624)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12624)Memory used [KB]: 6268
% 0.21/0.54  % (12624)Time elapsed: 0.118 s
% 0.21/0.54  % (12624)------------------------------
% 0.21/0.54  % (12624)------------------------------
% 0.21/0.54  % (12640)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (12619)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (12633)Refutation not found, incomplete strategy% (12633)------------------------------
% 0.21/0.54  % (12633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12618)Refutation not found, incomplete strategy% (12618)------------------------------
% 0.21/0.54  % (12618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12621)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (12631)Refutation not found, incomplete strategy% (12631)------------------------------
% 0.21/0.54  % (12631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12639)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (12625)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (12630)Refutation not found, incomplete strategy% (12630)------------------------------
% 0.21/0.54  % (12630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12634)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (12645)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (12622)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (12621)Refutation not found, incomplete strategy% (12621)------------------------------
% 0.21/0.54  % (12621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12631)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12631)Memory used [KB]: 10746
% 0.21/0.54  % (12631)Time elapsed: 0.110 s
% 0.21/0.54  % (12631)------------------------------
% 0.21/0.54  % (12631)------------------------------
% 0.21/0.54  % (12632)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (12645)Refutation not found, incomplete strategy% (12645)------------------------------
% 0.21/0.54  % (12645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12618)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12618)Memory used [KB]: 1791
% 0.21/0.54  % (12618)Time elapsed: 0.128 s
% 0.21/0.54  % (12618)------------------------------
% 0.21/0.54  % (12618)------------------------------
% 0.21/0.54  % (12637)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (12649)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (12632)Refutation not found, incomplete strategy% (12632)------------------------------
% 0.21/0.54  % (12632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12632)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12632)Memory used [KB]: 10618
% 0.21/0.54  % (12632)Time elapsed: 0.125 s
% 0.21/0.54  % (12632)------------------------------
% 0.21/0.54  % (12632)------------------------------
% 0.21/0.55  % (12633)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (12633)Memory used [KB]: 10746
% 0.21/0.55  % (12633)Time elapsed: 0.117 s
% 0.21/0.55  % (12633)------------------------------
% 0.21/0.55  % (12633)------------------------------
% 0.21/0.55  % (12638)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (12651)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (12636)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (12643)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (12650)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (12641)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (12630)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (12630)Memory used [KB]: 10746
% 0.21/0.55  % (12630)Time elapsed: 0.128 s
% 0.21/0.55  % (12630)------------------------------
% 0.21/0.55  % (12630)------------------------------
% 0.21/0.55  % (12647)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (12628)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (12648)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (12643)Refutation not found, incomplete strategy% (12643)------------------------------
% 0.21/0.55  % (12643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (12647)Refutation not found, incomplete strategy% (12647)------------------------------
% 0.21/0.56  % (12647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (12647)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (12647)Memory used [KB]: 6524
% 0.21/0.56  % (12647)Time elapsed: 0.143 s
% 0.21/0.56  % (12647)------------------------------
% 0.21/0.56  % (12647)------------------------------
% 0.21/0.56  % (12643)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (12643)Memory used [KB]: 1791
% 0.21/0.56  % (12643)Time elapsed: 0.140 s
% 0.21/0.56  % (12643)------------------------------
% 0.21/0.56  % (12643)------------------------------
% 0.21/0.56  % (12648)Refutation not found, incomplete strategy% (12648)------------------------------
% 0.21/0.56  % (12648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (12648)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (12648)Memory used [KB]: 10746
% 0.21/0.56  % (12648)Time elapsed: 0.140 s
% 0.21/0.56  % (12648)------------------------------
% 0.21/0.56  % (12648)------------------------------
% 0.21/0.56  % (12621)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (12621)Memory used [KB]: 10746
% 0.21/0.56  % (12621)Time elapsed: 0.130 s
% 0.21/0.56  % (12621)------------------------------
% 0.21/0.56  % (12621)------------------------------
% 0.21/0.56  % (12645)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  % (12639)Refutation not found, incomplete strategy% (12639)------------------------------
% 0.21/0.56  % (12639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (12625)Refutation not found, incomplete strategy% (12625)------------------------------
% 0.21/0.56  % (12625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  
% 0.21/0.57  % (12639)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (12645)Memory used [KB]: 1791
% 0.21/0.57  % (12639)Memory used [KB]: 10618
% 0.21/0.57  % (12645)Time elapsed: 0.133 s
% 0.21/0.57  % (12639)Time elapsed: 0.152 s
% 0.21/0.57  % (12645)------------------------------
% 0.21/0.57  % (12645)------------------------------
% 0.21/0.57  % (12639)------------------------------
% 0.21/0.57  % (12639)------------------------------
% 1.60/0.57  % (12646)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.60/0.57  % (12637)Refutation not found, incomplete strategy% (12637)------------------------------
% 1.60/0.57  % (12637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (12637)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.57  
% 1.60/0.57  % (12637)Memory used [KB]: 6140
% 1.60/0.57  % (12637)Time elapsed: 0.003 s
% 1.60/0.57  % (12637)------------------------------
% 1.60/0.57  % (12637)------------------------------
% 1.60/0.58  % SZS status CounterSatisfiable for theBenchmark
% 1.60/0.58  % (12626)# SZS output start Saturation.
% 1.60/0.58  cnf(u58,axiom,
% 1.60/0.58      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.60/0.58  
% 1.60/0.58  cnf(u32,negated_conjecture,
% 1.60/0.58      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.60/0.58  
% 1.60/0.58  cnf(u28,negated_conjecture,
% 1.60/0.58      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.60/0.58  
% 1.60/0.58  cnf(u241,negated_conjecture,
% 1.60/0.58      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2))).
% 1.60/0.58  
% 1.60/0.58  cnf(u242,negated_conjecture,
% 1.60/0.58      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k3_tarski(k2_tarski(X1,sK1))).
% 1.60/0.58  
% 1.60/0.58  cnf(u47,axiom,
% 1.60/0.58      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 1.60/0.58  
% 1.60/0.58  cnf(u56,axiom,
% 1.60/0.58      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))).
% 1.60/0.58  
% 1.60/0.58  cnf(u243,axiom,
% 1.60/0.58      ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k3_tarski(k2_tarski(X2,X3)) = k4_subset_1(X3,X2,X3)).
% 1.60/0.58  
% 1.60/0.58  cnf(u275,negated_conjecture,
% 1.60/0.58      r1_tarski(sK2,k2_struct_0(sK0))).
% 1.60/0.58  
% 1.60/0.58  cnf(u253,negated_conjecture,
% 1.60/0.58      r1_tarski(sK1,k2_struct_0(sK0))).
% 1.60/0.58  
% 1.60/0.58  cnf(u785,axiom,
% 1.60/0.58      r1_tarski(X0,k4_subset_1(X0,X0,X0))).
% 1.60/0.58  
% 1.60/0.58  cnf(u134,axiom,
% 1.60/0.58      r1_tarski(X8,k3_tarski(k2_tarski(X9,X8)))).
% 1.60/0.58  
% 1.60/0.58  cnf(u133,axiom,
% 1.60/0.58      r1_tarski(X6,k3_tarski(k2_tarski(X6,X7)))).
% 1.60/0.58  
% 1.60/0.58  cnf(u370,axiom,
% 1.60/0.58      r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X1)))).
% 1.60/0.58  
% 1.60/0.58  cnf(u105,axiom,
% 1.60/0.58      r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4)).
% 1.60/0.58  
% 1.60/0.58  cnf(u60,axiom,
% 1.60/0.58      r1_tarski(k1_xboole_0,X0)).
% 1.60/0.58  
% 1.60/0.58  cnf(u59,axiom,
% 1.60/0.58      r1_tarski(X0,X0)).
% 1.60/0.58  
% 1.60/0.58  cnf(u37,axiom,
% 1.60/0.58      r1_tarski(k4_xboole_0(X0,X1),X0)).
% 1.60/0.58  
% 1.60/0.58  cnf(u54,axiom,
% 1.60/0.58      ~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0).
% 1.60/0.58  
% 1.60/0.58  cnf(u61,negated_conjecture,
% 1.60/0.58      r1_xboole_0(sK2,sK1)).
% 1.60/0.58  
% 1.60/0.58  cnf(u30,negated_conjecture,
% 1.60/0.58      r1_xboole_0(sK1,sK2)).
% 1.60/0.58  
% 1.60/0.58  cnf(u45,axiom,
% 1.60/0.58      ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)).
% 1.60/0.58  
% 1.60/0.58  cnf(u55,axiom,
% 1.60/0.58      ~r1_xboole_0(X0,X1) | k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0).
% 1.60/0.58  
% 1.60/0.58  cnf(u240,axiom,
% 1.60/0.58      k4_xboole_0(X2,X3) = k7_subset_1(X2,X2,X3)).
% 1.60/0.58  
% 1.60/0.58  cnf(u781,negated_conjecture,
% 1.60/0.58      k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 1.60/0.58  
% 1.60/0.58  cnf(u780,negated_conjecture,
% 1.60/0.58      k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 1.60/0.58  
% 1.60/0.58  cnf(u782,axiom,
% 1.60/0.58      k3_tarski(k2_tarski(X0,X0)) = k4_subset_1(X0,X0,X0)).
% 1.60/0.58  
% 1.60/0.58  cnf(u784,negated_conjecture,
% 1.60/0.58      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1)).
% 1.60/0.58  
% 1.60/0.58  cnf(u783,negated_conjecture,
% 1.60/0.58      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2)).
% 1.60/0.58  
% 1.60/0.58  cnf(u336,negated_conjecture,
% 1.60/0.58      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 1.60/0.58  
% 1.60/0.58  cnf(u29,negated_conjecture,
% 1.60/0.58      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 1.60/0.58  
% 1.60/0.58  cnf(u337,negated_conjecture,
% 1.60/0.58      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))).
% 1.60/0.58  
% 1.60/0.58  % (12628)Refutation not found, incomplete strategy% (12628)------------------------------
% 1.60/0.58  % (12628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  cnf(u252,negated_conjecture,
% 1.60/0.58      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0)))).
% 1.60/0.58  
% 1.60/0.58  % (12628)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.58  
% 1.60/0.58  % (12628)Memory used [KB]: 6780
% 1.60/0.58  % (12628)Time elapsed: 0.154 s
% 1.60/0.58  % (12628)------------------------------
% 1.60/0.58  % (12628)------------------------------
% 1.60/0.58  cnf(u247,negated_conjecture,
% 1.60/0.58      k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2))).
% 1.60/0.58  
% 1.60/0.58  cnf(u52,axiom,
% 1.60/0.58      k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))).
% 1.60/0.58  
% 1.60/0.58  cnf(u248,negated_conjecture,
% 1.60/0.58      sK2 = k5_xboole_0(k2_struct_0(sK0),sK1)).
% 1.60/0.58  
% 1.60/0.58  cnf(u249,negated_conjecture,
% 1.60/0.58      sK1 = k5_xboole_0(k2_struct_0(sK0),sK2)).
% 1.60/0.58  
% 1.60/0.58  cnf(u805,axiom,
% 1.60/0.58      k4_xboole_0(k4_subset_1(X4,X4,X4),X4) = k5_xboole_0(k4_subset_1(X4,X4,X4),X4)).
% 1.60/0.58  
% 1.60/0.58  cnf(u185,axiom,
% 1.60/0.58      k4_xboole_0(k3_tarski(k2_tarski(X9,X8)),X8) = k5_xboole_0(k3_tarski(k2_tarski(X9,X8)),X8)).
% 1.60/0.58  
% 1.60/0.58  cnf(u184,axiom,
% 1.60/0.58      k4_xboole_0(k3_tarski(k2_tarski(X6,X7)),X6) = k5_xboole_0(k3_tarski(k2_tarski(X6,X7)),X6)).
% 1.60/0.58  
% 1.60/0.58  cnf(u1418,axiom,
% 1.60/0.58      k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X24)),k1_xboole_0) = k5_xboole_0(k4_xboole_0(X24,k4_xboole_0(X24,X23)),k1_xboole_0)).
% 1.60/0.58  
% 1.60/0.58  cnf(u973,axiom,
% 1.60/0.58      k4_xboole_0(X29,k4_xboole_0(X29,X30)) = k5_xboole_0(k4_xboole_0(X30,k4_xboole_0(X30,X29)),k1_xboole_0)).
% 1.60/0.58  
% 1.60/0.58  cnf(u775,axiom,
% 1.60/0.58      k1_xboole_0 = k5_xboole_0(k4_xboole_0(X20,k4_xboole_0(X20,X19)),k4_xboole_0(X19,k4_xboole_0(X19,X20)))).
% 1.60/0.58  
% 1.60/0.58  cnf(u465,axiom,
% 1.60/0.58      k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))).
% 1.60/0.58  
% 1.60/0.58  cnf(u78,axiom,
% 1.60/0.58      k1_xboole_0 = k5_xboole_0(X1,X1)).
% 1.60/0.58  
% 1.60/0.58  cnf(u354,axiom,
% 1.60/0.58      k4_xboole_0(X2,k4_xboole_0(X2,X3)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))).
% 1.60/0.58  
% 1.60/0.58  cnf(u103,axiom,
% 1.60/0.58      k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))).
% 1.60/0.58  
% 1.60/0.58  cnf(u49,axiom,
% 1.60/0.58      k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))).
% 1.60/0.58  
% 1.60/0.58  cnf(u250,negated_conjecture,
% 1.60/0.58      sK2 = k4_xboole_0(k2_struct_0(sK0),sK1)).
% 1.60/0.58  
% 1.60/0.58  cnf(u251,negated_conjecture,
% 1.60/0.58      sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)).
% 1.60/0.58  
% 1.60/0.58  cnf(u239,negated_conjecture,
% 1.60/0.58      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1)).
% 1.60/0.58  
% 1.60/0.58  cnf(u238,negated_conjecture,
% 1.60/0.58      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0)).
% 1.60/0.58  
% 1.60/0.58  cnf(u265,negated_conjecture,
% 1.60/0.58      k1_xboole_0 = k4_xboole_0(sK2,k2_struct_0(sK0))).
% 1.60/0.58  
% 1.60/0.58  cnf(u287,negated_conjecture,
% 1.60/0.58      k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0))).
% 1.60/0.58  
% 1.60/0.58  cnf(u89,axiom,
% 1.60/0.58      k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)).
% 1.60/0.58  
% 1.60/0.58  cnf(u762,axiom,
% 1.60/0.58      k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))).
% 1.60/0.58  
% 1.60/0.58  cnf(u386,axiom,
% 1.60/0.58      k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1)).
% 1.60/0.58  
% 1.60/0.58  cnf(u371,axiom,
% 1.60/0.58      k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,X11),X10)).
% 1.60/0.58  
% 1.60/0.58  cnf(u787,axiom,
% 1.60/0.58      k1_xboole_0 = k4_xboole_0(X2,k4_subset_1(X2,X2,X2))).
% 1.60/0.58  
% 1.60/0.58  cnf(u64,axiom,
% 1.60/0.58      k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_tarski(X1,X0)))).
% 1.60/0.58  
% 1.60/0.58  cnf(u51,axiom,
% 1.60/0.58      k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1)))).
% 1.60/0.58  
% 1.60/0.58  cnf(u57,axiom,
% 1.60/0.58      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 1.60/0.58  
% 1.60/0.58  cnf(u958,axiom,
% 1.60/0.58      k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X5)),k1_xboole_0)).
% 1.60/0.58  
% 1.60/0.58  cnf(u971,axiom,
% 1.60/0.58      k4_xboole_0(X27,k4_xboole_0(X27,X28)) = k4_xboole_0(k4_xboole_0(X28,k4_xboole_0(X28,X27)),k1_xboole_0)).
% 1.60/0.58  
% 1.60/0.58  cnf(u459,axiom,
% 1.60/0.58      k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k4_xboole_0(X10,X9)).
% 1.60/0.58  
% 1.60/0.58  cnf(u351,axiom,
% 1.60/0.58      k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3)))).
% 1.60/0.58  
% 1.60/0.58  cnf(u53,axiom,
% 1.60/0.58      k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))).
% 1.60/0.58  
% 1.60/0.58  cnf(u77,axiom,
% 1.60/0.58      k5_xboole_0(X0,k1_xboole_0) = X0).
% 1.60/0.58  
% 1.60/0.58  cnf(u35,axiom,
% 1.60/0.58      k4_xboole_0(X0,k1_xboole_0) = X0).
% 1.60/0.58  
% 1.60/0.58  cnf(u33,axiom,
% 1.60/0.58      k2_subset_1(X0) = X0).
% 1.60/0.58  
% 1.60/0.58  cnf(u31,negated_conjecture,
% 1.60/0.58      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 1.60/0.58  
% 1.60/0.58  % (12626)# SZS output end Saturation.
% 1.60/0.58  % (12626)------------------------------
% 1.60/0.58  % (12626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (12626)Termination reason: Satisfiable
% 1.60/0.58  
% 1.60/0.58  % (12626)Memory used [KB]: 6908
% 1.60/0.58  % (12626)Time elapsed: 0.109 s
% 1.60/0.58  % (12626)------------------------------
% 1.60/0.58  % (12626)------------------------------
% 1.60/0.58  % (12614)Success in time 0.21 s
%------------------------------------------------------------------------------

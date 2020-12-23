%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:41 EST 2020

% Result     : Theorem 5.22s
% Output     : Refutation 5.22s
% Verified   : 
% Statistics : Number of formulae       :   34 (  91 expanded)
%              Number of leaves         :    7 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   39 (  99 expanded)
%              Number of equality atoms :   28 (  85 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9807,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f9672,f9674])).

fof(f9674,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f9673])).

fof(f9673,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f9397,f8326])).

fof(f8326,plain,(
    ! [X8,X7,X9] : k2_xboole_0(X7,k3_xboole_0(X8,X9)) = k2_xboole_0(X7,k3_xboole_0(X9,X8)) ),
    inference(superposition,[],[f1293,f262])).

fof(f262,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X1,k3_xboole_0(X0,X2)) = k2_xboole_0(X1,k3_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f41,f10])).

fof(f10,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f41,plain,(
    ! [X2,X3,X1] : k2_xboole_0(X1,k2_xboole_0(k3_xboole_0(X2,X1),X3)) = k2_xboole_0(X1,X3) ),
    inference(superposition,[],[f11,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f12,f14])).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f11,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f1293,plain,(
    ! [X14,X15,X16] : k2_xboole_0(X15,k3_xboole_0(X16,X14)) = k2_xboole_0(X15,k3_xboole_0(X14,k2_xboole_0(X15,X16))) ),
    inference(superposition,[],[f41,f95])).

fof(f95,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X5,k2_xboole_0(X7,X6)) = k2_xboole_0(k3_xboole_0(X5,X7),k3_xboole_0(X6,X5)) ),
    inference(superposition,[],[f10,f14])).

fof(f9397,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK2,sK1))
    | spl3_1 ),
    inference(superposition,[],[f18,f2769])).

fof(f2769,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f2696,f262])).

fof(f2696,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f632,f13])).

fof(f13,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f632,plain,(
    ! [X10,X8,X9] : k3_xboole_0(X8,k2_xboole_0(X10,X9)) = k2_xboole_0(k3_xboole_0(X10,X8),k3_xboole_0(X9,X8)) ),
    inference(superposition,[],[f91,f14])).

fof(f91,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(k3_xboole_0(X6,X5),k3_xboole_0(X5,X7)) ),
    inference(superposition,[],[f10,f14])).

fof(f18,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f16,plain,
    ( spl3_1
  <=> k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f9672,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f9671])).

fof(f9671,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f18,f9395])).

fof(f9395,plain,(
    ! [X26,X24,X25] : k3_xboole_0(k2_xboole_0(X24,X26),k2_xboole_0(X24,X25)) = k2_xboole_0(X24,k3_xboole_0(X26,X25)) ),
    inference(superposition,[],[f2769,f14])).

fof(f19,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f9,f16])).

fof(f9,plain,(
    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:59:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (9510)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.42  % (9509)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (9508)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.44  % (9511)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.47  % (9504)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.47  % (9505)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.47  % (9507)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.48  % (9506)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.48  % (9513)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.48  % (9512)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.49  % (9515)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.49  % (9514)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 5.22/1.02  % (9505)Time limit reached!
% 5.22/1.02  % (9505)------------------------------
% 5.22/1.02  % (9505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.22/1.02  % (9505)Termination reason: Time limit
% 5.22/1.02  % (9505)Termination phase: Saturation
% 5.22/1.02  
% 5.22/1.02  % (9505)Memory used [KB]: 20084
% 5.22/1.02  % (9505)Time elapsed: 0.600 s
% 5.22/1.02  % (9505)------------------------------
% 5.22/1.02  % (9505)------------------------------
% 5.22/1.03  % (9512)Refutation found. Thanks to Tanya!
% 5.22/1.03  % SZS status Theorem for theBenchmark
% 5.22/1.03  % SZS output start Proof for theBenchmark
% 5.22/1.03  fof(f9807,plain,(
% 5.22/1.03    $false),
% 5.22/1.03    inference(avatar_sat_refutation,[],[f19,f9672,f9674])).
% 5.22/1.03  fof(f9674,plain,(
% 5.22/1.03    spl3_1),
% 5.22/1.03    inference(avatar_contradiction_clause,[],[f9673])).
% 5.22/1.03  fof(f9673,plain,(
% 5.22/1.03    $false | spl3_1),
% 5.22/1.03    inference(subsumption_resolution,[],[f9397,f8326])).
% 5.22/1.03  fof(f8326,plain,(
% 5.22/1.03    ( ! [X8,X7,X9] : (k2_xboole_0(X7,k3_xboole_0(X8,X9)) = k2_xboole_0(X7,k3_xboole_0(X9,X8))) )),
% 5.22/1.03    inference(superposition,[],[f1293,f262])).
% 5.22/1.03  fof(f262,plain,(
% 5.22/1.03    ( ! [X2,X0,X1] : (k2_xboole_0(X1,k3_xboole_0(X0,X2)) = k2_xboole_0(X1,k3_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 5.22/1.03    inference(superposition,[],[f41,f10])).
% 5.22/1.03  fof(f10,plain,(
% 5.22/1.03    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 5.22/1.03    inference(cnf_transformation,[],[f4])).
% 5.22/1.03  fof(f4,axiom,(
% 5.22/1.03    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 5.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 5.22/1.03  fof(f41,plain,(
% 5.22/1.03    ( ! [X2,X3,X1] : (k2_xboole_0(X1,k2_xboole_0(k3_xboole_0(X2,X1),X3)) = k2_xboole_0(X1,X3)) )),
% 5.22/1.03    inference(superposition,[],[f11,f24])).
% 5.22/1.03  fof(f24,plain,(
% 5.22/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 5.22/1.03    inference(superposition,[],[f12,f14])).
% 5.22/1.03  fof(f14,plain,(
% 5.22/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.22/1.03    inference(cnf_transformation,[],[f1])).
% 5.22/1.03  fof(f1,axiom,(
% 5.22/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.22/1.03  fof(f12,plain,(
% 5.22/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 5.22/1.03    inference(cnf_transformation,[],[f3])).
% 5.22/1.03  fof(f3,axiom,(
% 5.22/1.03    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 5.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 5.22/1.03  fof(f11,plain,(
% 5.22/1.03    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 5.22/1.03    inference(cnf_transformation,[],[f5])).
% 5.22/1.03  fof(f5,axiom,(
% 5.22/1.03    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 5.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 5.22/1.03  fof(f1293,plain,(
% 5.22/1.03    ( ! [X14,X15,X16] : (k2_xboole_0(X15,k3_xboole_0(X16,X14)) = k2_xboole_0(X15,k3_xboole_0(X14,k2_xboole_0(X15,X16)))) )),
% 5.22/1.03    inference(superposition,[],[f41,f95])).
% 5.22/1.03  fof(f95,plain,(
% 5.22/1.03    ( ! [X6,X7,X5] : (k3_xboole_0(X5,k2_xboole_0(X7,X6)) = k2_xboole_0(k3_xboole_0(X5,X7),k3_xboole_0(X6,X5))) )),
% 5.22/1.03    inference(superposition,[],[f10,f14])).
% 5.22/1.03  fof(f9397,plain,(
% 5.22/1.03    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) | spl3_1),
% 5.22/1.03    inference(superposition,[],[f18,f2769])).
% 5.22/1.03  fof(f2769,plain,(
% 5.22/1.03    ( ! [X2,X0,X1] : (k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X2,X1))) )),
% 5.22/1.03    inference(forward_demodulation,[],[f2696,f262])).
% 5.22/1.03  fof(f2696,plain,(
% 5.22/1.03    ( ! [X2,X0,X1] : (k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X2,k2_xboole_0(X0,X1)))) )),
% 5.22/1.03    inference(superposition,[],[f632,f13])).
% 5.22/1.03  fof(f13,plain,(
% 5.22/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 5.22/1.03    inference(cnf_transformation,[],[f2])).
% 5.22/1.03  fof(f2,axiom,(
% 5.22/1.03    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 5.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 5.22/1.03  fof(f632,plain,(
% 5.22/1.03    ( ! [X10,X8,X9] : (k3_xboole_0(X8,k2_xboole_0(X10,X9)) = k2_xboole_0(k3_xboole_0(X10,X8),k3_xboole_0(X9,X8))) )),
% 5.22/1.03    inference(superposition,[],[f91,f14])).
% 5.22/1.03  fof(f91,plain,(
% 5.22/1.03    ( ! [X6,X7,X5] : (k3_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(k3_xboole_0(X6,X5),k3_xboole_0(X5,X7))) )),
% 5.22/1.03    inference(superposition,[],[f10,f14])).
% 5.22/1.03  fof(f18,plain,(
% 5.22/1.03    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) | spl3_1),
% 5.22/1.03    inference(avatar_component_clause,[],[f16])).
% 5.22/1.03  fof(f16,plain,(
% 5.22/1.03    spl3_1 <=> k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 5.22/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 5.22/1.03  fof(f9672,plain,(
% 5.22/1.03    spl3_1),
% 5.22/1.03    inference(avatar_contradiction_clause,[],[f9671])).
% 5.22/1.03  fof(f9671,plain,(
% 5.22/1.03    $false | spl3_1),
% 5.22/1.03    inference(subsumption_resolution,[],[f18,f9395])).
% 5.22/1.03  fof(f9395,plain,(
% 5.22/1.03    ( ! [X26,X24,X25] : (k3_xboole_0(k2_xboole_0(X24,X26),k2_xboole_0(X24,X25)) = k2_xboole_0(X24,k3_xboole_0(X26,X25))) )),
% 5.22/1.03    inference(superposition,[],[f2769,f14])).
% 5.22/1.03  fof(f19,plain,(
% 5.22/1.03    ~spl3_1),
% 5.22/1.03    inference(avatar_split_clause,[],[f9,f16])).
% 5.22/1.03  fof(f9,plain,(
% 5.22/1.03    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 5.22/1.03    inference(cnf_transformation,[],[f8])).
% 5.22/1.03  fof(f8,plain,(
% 5.22/1.03    ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 5.22/1.03    inference(ennf_transformation,[],[f7])).
% 5.22/1.03  fof(f7,negated_conjecture,(
% 5.22/1.03    ~! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 5.22/1.03    inference(negated_conjecture,[],[f6])).
% 5.22/1.03  fof(f6,conjecture,(
% 5.22/1.03    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 5.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).
% 5.22/1.03  % SZS output end Proof for theBenchmark
% 5.22/1.03  % (9512)------------------------------
% 5.22/1.03  % (9512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.22/1.03  % (9512)Termination reason: Refutation
% 5.22/1.03  
% 5.22/1.03  % (9512)Memory used [KB]: 16502
% 5.22/1.03  % (9512)Time elapsed: 0.610 s
% 5.22/1.03  % (9512)------------------------------
% 5.22/1.03  % (9512)------------------------------
% 5.22/1.03  % (9503)Success in time 0.667 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:41 EST 2020

% Result     : Theorem 5.02s
% Output     : Refutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 105 expanded)
%              Number of leaves         :    7 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   42 ( 113 expanded)
%              Number of equality atoms :   31 (  99 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9582,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f9449,f9451])).

fof(f9451,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f9450])).

fof(f9450,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f9172,f7099])).

fof(f7099,plain,(
    ! [X8,X7,X9] : k2_xboole_0(X7,k3_xboole_0(X8,X9)) = k2_xboole_0(X7,k3_xboole_0(X9,X8)) ),
    inference(superposition,[],[f820,f311])).

fof(f311,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X1,k3_xboole_0(X0,X2)) = k2_xboole_0(X1,k3_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f28,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f28,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(k3_xboole_0(X4,X3),X5)) = k2_xboole_0(X3,X5) ),
    inference(superposition,[],[f14,f22])).

fof(f22,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(superposition,[],[f15,f11])).

fof(f11,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f820,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X9,k3_xboole_0(X10,X8)) = k2_xboole_0(X9,k3_xboole_0(X8,k2_xboole_0(X9,X10))) ),
    inference(superposition,[],[f28,f95])).

fof(f95,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X2,k2_xboole_0(X4,X3)) = k2_xboole_0(k3_xboole_0(X2,X4),k3_xboole_0(X3,X2)) ),
    inference(superposition,[],[f13,f11])).

fof(f9172,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK2,sK1))
    | spl3_1 ),
    inference(superposition,[],[f19,f2888])).

fof(f2888,plain,(
    ! [X10,X8,X9] : k3_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X8,X10)) = k2_xboole_0(X8,k3_xboole_0(X10,X9)) ),
    inference(forward_demodulation,[],[f2817,f311])).

fof(f2817,plain,(
    ! [X10,X8,X9] : k3_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X8,X10)) = k2_xboole_0(X8,k3_xboole_0(X10,k2_xboole_0(X8,X9))) ),
    inference(superposition,[],[f552,f106])).

fof(f106,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f91,f15])).

fof(f91,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f13,f12])).

fof(f12,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f552,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X2,k2_xboole_0(X4,X3)) = k2_xboole_0(k3_xboole_0(X4,X2),k3_xboole_0(X3,X2)) ),
    inference(superposition,[],[f92,f11])).

fof(f92,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X2,k2_xboole_0(X3,X4)) = k2_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X2,X4)) ),
    inference(superposition,[],[f13,f11])).

fof(f19,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f17,plain,
    ( spl3_1
  <=> k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f9449,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f9448])).

fof(f9448,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f19,f9170])).

fof(f9170,plain,(
    ! [X28,X29,X27] : k3_xboole_0(k2_xboole_0(X27,X29),k2_xboole_0(X27,X28)) = k2_xboole_0(X27,k3_xboole_0(X29,X28)) ),
    inference(superposition,[],[f2888,f11])).

fof(f20,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f10,f17])).

fof(f10,plain,(
    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:57:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.40  % (9744)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.19/0.41  % (9747)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.19/0.41  % (9746)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.19/0.45  % (9745)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.19/0.45  % (9741)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.19/0.45  % (9740)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.19/0.46  % (9743)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.19/0.46  % (9742)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.19/0.46  % (9750)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.19/0.47  % (9748)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.19/0.47  % (9751)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.19/0.47  % (9749)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 5.02/1.01  % (9741)Time limit reached!
% 5.02/1.01  % (9741)------------------------------
% 5.02/1.01  % (9741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.02/1.01  % (9741)Termination reason: Time limit
% 5.02/1.01  % (9741)Termination phase: Saturation
% 5.02/1.01  
% 5.02/1.01  % (9741)Memory used [KB]: 23283
% 5.02/1.01  % (9741)Time elapsed: 0.600 s
% 5.02/1.01  % (9741)------------------------------
% 5.02/1.01  % (9741)------------------------------
% 5.02/1.03  % (9748)Refutation found. Thanks to Tanya!
% 5.02/1.03  % SZS status Theorem for theBenchmark
% 5.02/1.03  % SZS output start Proof for theBenchmark
% 5.02/1.03  fof(f9582,plain,(
% 5.02/1.03    $false),
% 5.02/1.03    inference(avatar_sat_refutation,[],[f20,f9449,f9451])).
% 5.02/1.03  fof(f9451,plain,(
% 5.02/1.03    spl3_1),
% 5.02/1.03    inference(avatar_contradiction_clause,[],[f9450])).
% 5.02/1.03  fof(f9450,plain,(
% 5.02/1.03    $false | spl3_1),
% 5.02/1.03    inference(subsumption_resolution,[],[f9172,f7099])).
% 5.02/1.03  fof(f7099,plain,(
% 5.02/1.03    ( ! [X8,X7,X9] : (k2_xboole_0(X7,k3_xboole_0(X8,X9)) = k2_xboole_0(X7,k3_xboole_0(X9,X8))) )),
% 5.02/1.03    inference(superposition,[],[f820,f311])).
% 5.02/1.03  fof(f311,plain,(
% 5.02/1.03    ( ! [X2,X0,X1] : (k2_xboole_0(X1,k3_xboole_0(X0,X2)) = k2_xboole_0(X1,k3_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 5.02/1.03    inference(superposition,[],[f28,f13])).
% 5.02/1.03  fof(f13,plain,(
% 5.02/1.03    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 5.02/1.03    inference(cnf_transformation,[],[f4])).
% 5.02/1.03  fof(f4,axiom,(
% 5.02/1.03    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 5.02/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 5.02/1.03  fof(f28,plain,(
% 5.02/1.03    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k2_xboole_0(k3_xboole_0(X4,X3),X5)) = k2_xboole_0(X3,X5)) )),
% 5.02/1.03    inference(superposition,[],[f14,f22])).
% 5.02/1.03  fof(f22,plain,(
% 5.02/1.03    ( ! [X2,X1] : (k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1) )),
% 5.02/1.03    inference(superposition,[],[f15,f11])).
% 5.02/1.03  fof(f11,plain,(
% 5.02/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.02/1.03    inference(cnf_transformation,[],[f1])).
% 5.02/1.03  fof(f1,axiom,(
% 5.02/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.02/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.02/1.03  fof(f15,plain,(
% 5.02/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 5.02/1.03    inference(cnf_transformation,[],[f3])).
% 5.02/1.03  fof(f3,axiom,(
% 5.02/1.03    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 5.02/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 5.02/1.03  fof(f14,plain,(
% 5.02/1.03    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 5.02/1.03    inference(cnf_transformation,[],[f5])).
% 5.02/1.03  fof(f5,axiom,(
% 5.02/1.03    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 5.02/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 5.02/1.03  fof(f820,plain,(
% 5.02/1.03    ( ! [X10,X8,X9] : (k2_xboole_0(X9,k3_xboole_0(X10,X8)) = k2_xboole_0(X9,k3_xboole_0(X8,k2_xboole_0(X9,X10)))) )),
% 5.02/1.03    inference(superposition,[],[f28,f95])).
% 5.02/1.03  fof(f95,plain,(
% 5.02/1.03    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X4,X3)) = k2_xboole_0(k3_xboole_0(X2,X4),k3_xboole_0(X3,X2))) )),
% 5.02/1.03    inference(superposition,[],[f13,f11])).
% 5.02/1.03  fof(f9172,plain,(
% 5.02/1.03    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) | spl3_1),
% 5.02/1.03    inference(superposition,[],[f19,f2888])).
% 5.02/1.03  fof(f2888,plain,(
% 5.02/1.03    ( ! [X10,X8,X9] : (k3_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X8,X10)) = k2_xboole_0(X8,k3_xboole_0(X10,X9))) )),
% 5.02/1.03    inference(forward_demodulation,[],[f2817,f311])).
% 5.02/1.03  fof(f2817,plain,(
% 5.02/1.03    ( ! [X10,X8,X9] : (k3_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X8,X10)) = k2_xboole_0(X8,k3_xboole_0(X10,k2_xboole_0(X8,X9)))) )),
% 5.02/1.03    inference(superposition,[],[f552,f106])).
% 5.02/1.03  fof(f106,plain,(
% 5.02/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 5.02/1.03    inference(forward_demodulation,[],[f91,f15])).
% 5.02/1.03  fof(f91,plain,(
% 5.02/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 5.02/1.03    inference(superposition,[],[f13,f12])).
% 5.02/1.03  fof(f12,plain,(
% 5.02/1.03    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 5.02/1.03    inference(cnf_transformation,[],[f8])).
% 5.02/1.03  fof(f8,plain,(
% 5.02/1.03    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 5.02/1.03    inference(rectify,[],[f2])).
% 5.02/1.03  fof(f2,axiom,(
% 5.02/1.03    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 5.02/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 5.02/1.03  fof(f552,plain,(
% 5.02/1.03    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X4,X3)) = k2_xboole_0(k3_xboole_0(X4,X2),k3_xboole_0(X3,X2))) )),
% 5.02/1.03    inference(superposition,[],[f92,f11])).
% 5.02/1.03  fof(f92,plain,(
% 5.02/1.03    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X3,X4)) = k2_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X2,X4))) )),
% 5.02/1.03    inference(superposition,[],[f13,f11])).
% 5.02/1.03  fof(f19,plain,(
% 5.02/1.03    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) | spl3_1),
% 5.02/1.03    inference(avatar_component_clause,[],[f17])).
% 5.02/1.03  fof(f17,plain,(
% 5.02/1.03    spl3_1 <=> k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 5.02/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 5.02/1.03  fof(f9449,plain,(
% 5.02/1.03    spl3_1),
% 5.02/1.03    inference(avatar_contradiction_clause,[],[f9448])).
% 5.02/1.03  fof(f9448,plain,(
% 5.02/1.03    $false | spl3_1),
% 5.02/1.03    inference(subsumption_resolution,[],[f19,f9170])).
% 5.02/1.03  fof(f9170,plain,(
% 5.02/1.03    ( ! [X28,X29,X27] : (k3_xboole_0(k2_xboole_0(X27,X29),k2_xboole_0(X27,X28)) = k2_xboole_0(X27,k3_xboole_0(X29,X28))) )),
% 5.02/1.03    inference(superposition,[],[f2888,f11])).
% 5.02/1.03  fof(f20,plain,(
% 5.02/1.03    ~spl3_1),
% 5.02/1.03    inference(avatar_split_clause,[],[f10,f17])).
% 5.02/1.03  fof(f10,plain,(
% 5.02/1.03    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 5.02/1.03    inference(cnf_transformation,[],[f9])).
% 5.02/1.03  fof(f9,plain,(
% 5.02/1.03    ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 5.02/1.03    inference(ennf_transformation,[],[f7])).
% 5.02/1.03  fof(f7,negated_conjecture,(
% 5.02/1.03    ~! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 5.02/1.03    inference(negated_conjecture,[],[f6])).
% 5.02/1.03  fof(f6,conjecture,(
% 5.02/1.03    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 5.02/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).
% 5.02/1.03  % SZS output end Proof for theBenchmark
% 5.02/1.03  % (9748)------------------------------
% 5.02/1.03  % (9748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.02/1.03  % (9748)Termination reason: Refutation
% 5.02/1.03  
% 5.02/1.03  % (9748)Memory used [KB]: 16502
% 5.02/1.03  % (9748)Time elapsed: 0.608 s
% 5.02/1.03  % (9748)------------------------------
% 5.02/1.03  % (9748)------------------------------
% 5.02/1.03  % (9739)Success in time 0.685 s
%------------------------------------------------------------------------------

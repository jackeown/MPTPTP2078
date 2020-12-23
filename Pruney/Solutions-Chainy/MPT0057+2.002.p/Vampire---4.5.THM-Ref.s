%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:09 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   41 (  76 expanded)
%              Number of leaves         :   10 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :   47 (  86 expanded)
%              Number of equality atoms :   36 (  71 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f310,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f65,f309])).

fof(f309,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f30,f307])).

fof(f307,plain,(
    ! [X10,X11,X9] : k4_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X9,X11)) = k3_xboole_0(X9,k4_xboole_0(X10,X11)) ),
    inference(forward_demodulation,[],[f306,f298])).

fof(f298,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,X2),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f161,f101])).

fof(f101,plain,(
    ! [X14,X15] : k4_xboole_0(k3_xboole_0(X14,X15),X14) = k4_xboole_0(X14,X14) ),
    inference(superposition,[],[f38,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f67,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f18,f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f18,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f24,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f161,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[],[f88,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f20,f23])).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f88,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(forward_demodulation,[],[f70,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f22,f26])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f18,f23])).

fof(f306,plain,(
    ! [X10,X11,X9] : k4_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X9,X11)) = k2_xboole_0(k4_xboole_0(X9,X9),k3_xboole_0(X9,k4_xboole_0(X10,X11))) ),
    inference(forward_demodulation,[],[f301,f20])).

fof(f301,plain,(
    ! [X10,X11,X9] : k4_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X9,X11)) = k2_xboole_0(k4_xboole_0(X9,X9),k4_xboole_0(k3_xboole_0(X9,X10),X11)) ),
    inference(superposition,[],[f19,f101])).

fof(f19,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f30,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_1
  <=> k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f65,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f54,f28,f62])).

fof(f62,plain,
    ( spl3_2
  <=> k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f54,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK2)))
    | spl3_1 ),
    inference(superposition,[],[f30,f20])).

fof(f31,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f28])).

fof(f17,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:24:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (23690)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (23687)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.43  % (23686)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.44  % (23693)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.44  % (23691)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.45  % (23684)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.45  % (23688)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.45  % (23695)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.48  % (23689)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.48  % (23696)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.49  % (23692)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.51  % (23694)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 1.54/0.61  % (23693)Refutation found. Thanks to Tanya!
% 1.54/0.61  % SZS status Theorem for theBenchmark
% 1.54/0.61  % SZS output start Proof for theBenchmark
% 1.54/0.61  fof(f310,plain,(
% 1.54/0.61    $false),
% 1.54/0.61    inference(avatar_sat_refutation,[],[f31,f65,f309])).
% 1.54/0.61  fof(f309,plain,(
% 1.54/0.61    spl3_1),
% 1.54/0.61    inference(avatar_contradiction_clause,[],[f308])).
% 1.54/0.61  fof(f308,plain,(
% 1.54/0.61    $false | spl3_1),
% 1.54/0.61    inference(subsumption_resolution,[],[f30,f307])).
% 1.54/0.61  fof(f307,plain,(
% 1.54/0.61    ( ! [X10,X11,X9] : (k4_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X9,X11)) = k3_xboole_0(X9,k4_xboole_0(X10,X11))) )),
% 1.54/0.61    inference(forward_demodulation,[],[f306,f298])).
% 1.54/0.61  fof(f298,plain,(
% 1.54/0.61    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,X2),k3_xboole_0(X2,X3))) )),
% 1.54/0.61    inference(superposition,[],[f161,f101])).
% 1.54/0.61  fof(f101,plain,(
% 1.54/0.61    ( ! [X14,X15] : (k4_xboole_0(k3_xboole_0(X14,X15),X14) = k4_xboole_0(X14,X14)) )),
% 1.54/0.61    inference(superposition,[],[f38,f83])).
% 1.54/0.61  fof(f83,plain,(
% 1.54/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.54/0.61    inference(forward_demodulation,[],[f67,f22])).
% 1.54/0.61  fof(f22,plain,(
% 1.54/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.54/0.61    inference(cnf_transformation,[],[f5])).
% 1.54/0.61  fof(f5,axiom,(
% 1.54/0.61    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.54/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.54/0.61  fof(f67,plain,(
% 1.54/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.54/0.61    inference(superposition,[],[f18,f23])).
% 1.54/0.61  fof(f23,plain,(
% 1.54/0.61    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.54/0.61    inference(cnf_transformation,[],[f15])).
% 1.54/0.61  fof(f15,plain,(
% 1.54/0.61    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.54/0.61    inference(rectify,[],[f2])).
% 1.54/0.61  fof(f2,axiom,(
% 1.54/0.61    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.54/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.54/0.61  fof(f18,plain,(
% 1.54/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.54/0.61    inference(cnf_transformation,[],[f6])).
% 1.54/0.61  fof(f6,axiom,(
% 1.54/0.61    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.54/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 1.54/0.61  fof(f38,plain,(
% 1.54/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 1.54/0.61    inference(superposition,[],[f24,f26])).
% 1.54/0.61  fof(f26,plain,(
% 1.54/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.54/0.61    inference(cnf_transformation,[],[f1])).
% 1.54/0.61  fof(f1,axiom,(
% 1.54/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.54/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.54/0.61  fof(f24,plain,(
% 1.54/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.54/0.61    inference(cnf_transformation,[],[f7])).
% 1.54/0.61  fof(f7,axiom,(
% 1.54/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.54/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.54/0.61  fof(f161,plain,(
% 1.54/0.61    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 1.54/0.61    inference(superposition,[],[f88,f46])).
% 1.54/0.61  fof(f46,plain,(
% 1.54/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.54/0.61    inference(superposition,[],[f20,f23])).
% 1.54/0.61  fof(f20,plain,(
% 1.54/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.54/0.61    inference(cnf_transformation,[],[f10])).
% 1.54/0.61  fof(f10,axiom,(
% 1.54/0.61    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.54/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.54/0.61  fof(f88,plain,(
% 1.54/0.61    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) )),
% 1.54/0.61    inference(forward_demodulation,[],[f70,f32])).
% 1.54/0.61  fof(f32,plain,(
% 1.54/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0) )),
% 1.54/0.61    inference(superposition,[],[f22,f26])).
% 1.54/0.61  fof(f70,plain,(
% 1.54/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 1.54/0.61    inference(superposition,[],[f18,f23])).
% 1.54/0.61  fof(f306,plain,(
% 1.54/0.61    ( ! [X10,X11,X9] : (k4_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X9,X11)) = k2_xboole_0(k4_xboole_0(X9,X9),k3_xboole_0(X9,k4_xboole_0(X10,X11)))) )),
% 1.54/0.61    inference(forward_demodulation,[],[f301,f20])).
% 1.54/0.61  fof(f301,plain,(
% 1.54/0.61    ( ! [X10,X11,X9] : (k4_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X9,X11)) = k2_xboole_0(k4_xboole_0(X9,X9),k4_xboole_0(k3_xboole_0(X9,X10),X11))) )),
% 1.54/0.61    inference(superposition,[],[f19,f101])).
% 1.54/0.61  fof(f19,plain,(
% 1.54/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 1.54/0.61    inference(cnf_transformation,[],[f3])).
% 1.54/0.61  fof(f3,axiom,(
% 1.54/0.61    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.54/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).
% 1.54/0.61  fof(f30,plain,(
% 1.54/0.61    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) | spl3_1),
% 1.54/0.61    inference(avatar_component_clause,[],[f28])).
% 1.54/0.61  fof(f28,plain,(
% 1.54/0.61    spl3_1 <=> k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.54/0.61  fof(f65,plain,(
% 1.54/0.61    ~spl3_2 | spl3_1),
% 1.54/0.61    inference(avatar_split_clause,[],[f54,f28,f62])).
% 1.54/0.61  fof(f62,plain,(
% 1.54/0.61    spl3_2 <=> k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK2)))),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.54/0.61  fof(f54,plain,(
% 1.54/0.61    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK2))) | spl3_1),
% 1.54/0.61    inference(superposition,[],[f30,f20])).
% 1.54/0.61  fof(f31,plain,(
% 1.54/0.61    ~spl3_1),
% 1.54/0.61    inference(avatar_split_clause,[],[f17,f28])).
% 1.54/0.61  fof(f17,plain,(
% 1.54/0.61    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 1.54/0.61    inference(cnf_transformation,[],[f16])).
% 1.54/0.61  fof(f16,plain,(
% 1.54/0.61    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.54/0.61    inference(ennf_transformation,[],[f14])).
% 1.54/0.61  fof(f14,negated_conjecture,(
% 1.54/0.61    ~! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.54/0.61    inference(negated_conjecture,[],[f13])).
% 1.54/0.61  fof(f13,conjecture,(
% 1.54/0.61    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.54/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).
% 1.54/0.61  % SZS output end Proof for theBenchmark
% 1.54/0.61  % (23693)------------------------------
% 1.54/0.61  % (23693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.61  % (23693)Termination reason: Refutation
% 1.54/0.61  
% 1.54/0.61  % (23693)Memory used [KB]: 6396
% 1.54/0.61  % (23693)Time elapsed: 0.177 s
% 1.54/0.61  % (23693)------------------------------
% 1.54/0.61  % (23693)------------------------------
% 1.54/0.62  % (23683)Success in time 0.262 s
%------------------------------------------------------------------------------

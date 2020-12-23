%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 132 expanded)
%              Number of leaves         :   11 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :   47 ( 133 expanded)
%              Number of equality atoms :   46 ( 132 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f341,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f339])).

fof(f339,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f26,f299])).

fof(f299,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,X9))) ),
    inference(forward_demodulation,[],[f298,f69])).

fof(f69,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f37,f68])).

fof(f68,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f50,f27])).

fof(f27,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f16,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f29,f17])).

fof(f17,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f19,f21,f21])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f36,f17])).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)),k1_xboole_0) ),
    inference(superposition,[],[f27,f28])).

fof(f28,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f18,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f298,plain,(
    ! [X8,X9] : k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,X9))) = k5_xboole_0(k4_xboole_0(X8,X9),k1_xboole_0) ),
    inference(forward_demodulation,[],[f281,f160])).

fof(f160,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(superposition,[],[f31,f61])).

fof(f61,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(superposition,[],[f28,f29])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f24,f21])).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f281,plain,(
    ! [X8,X9] : k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,X9))) = k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X8)) ),
    inference(superposition,[],[f209,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f209,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(backward_demodulation,[],[f25,f208])).

fof(f208,plain,(
    ! [X10,X8,X9] : k4_xboole_0(X10,X8) = k4_xboole_0(k4_xboole_0(X10,X8),k4_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f202,f69])).

fof(f202,plain,(
    ! [X10,X8,X9] : k4_xboole_0(k4_xboole_0(X10,X8),k4_xboole_0(X8,X9)) = k4_xboole_0(X10,k5_xboole_0(X8,k1_xboole_0)) ),
    inference(superposition,[],[f31,f160])).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f26,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f15,f20])).

fof(f15,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:16:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (23824)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (23828)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (23821)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (23831)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (23819)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (23820)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (23835)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (23827)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (23832)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (23831)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (23834)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (23823)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (23833)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (23822)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (23825)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (23818)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (23830)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f341,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f339])).
% 0.21/0.51  fof(f339,plain,(
% 0.21/0.51    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)),
% 0.21/0.51    inference(superposition,[],[f26,f299])).
% 0.21/0.51  fof(f299,plain,(
% 0.21/0.51    ( ! [X8,X9] : (k4_xboole_0(X8,X9) = k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,X9)))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f298,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(backward_demodulation,[],[f37,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.51    inference(forward_demodulation,[],[f50,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 0.21/0.51    inference(definition_unfolding,[],[f16,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(superposition,[],[f29,f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f19,f21,f21])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k1_xboole_0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f36,f17])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)),k1_xboole_0)) )),
% 0.21/0.51    inference(superposition,[],[f27,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f18,f21])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.51  fof(f298,plain,(
% 0.21/0.51    ( ! [X8,X9] : (k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,X9))) = k5_xboole_0(k4_xboole_0(X8,X9),k1_xboole_0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f281,f160])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 0.21/0.51    inference(superposition,[],[f31,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,X2)))) )),
% 0.21/0.51    inference(superposition,[],[f28,f29])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f24,f21])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.51  fof(f281,plain,(
% 0.21/0.51    ( ! [X8,X9] : (k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,X9))) = k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X8))) )),
% 0.21/0.51    inference(superposition,[],[f209,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f22,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.21/0.51    inference(backward_demodulation,[],[f25,f208])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    ( ! [X10,X8,X9] : (k4_xboole_0(X10,X8) = k4_xboole_0(k4_xboole_0(X10,X8),k4_xboole_0(X8,X9))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f202,f69])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    ( ! [X10,X8,X9] : (k4_xboole_0(k4_xboole_0(X10,X8),k4_xboole_0(X8,X9)) = k4_xboole_0(X10,k5_xboole_0(X8,k1_xboole_0))) )),
% 0.21/0.51    inference(superposition,[],[f31,f160])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f23,f21])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.21/0.51    inference(definition_unfolding,[],[f15,f20])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    inference(negated_conjecture,[],[f10])).
% 0.21/0.51  fof(f10,conjecture,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (23831)------------------------------
% 0.21/0.51  % (23831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23831)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (23831)Memory used [KB]: 1791
% 0.21/0.51  % (23831)Time elapsed: 0.079 s
% 0.21/0.51  % (23831)------------------------------
% 0.21/0.51  % (23831)------------------------------
% 0.21/0.51  % (23817)Success in time 0.146 s
%------------------------------------------------------------------------------

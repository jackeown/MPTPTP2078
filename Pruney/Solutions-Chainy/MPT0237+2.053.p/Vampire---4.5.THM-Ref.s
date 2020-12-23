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
% DateTime   : Thu Dec  3 12:37:36 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   32 (  93 expanded)
%              Number of leaves         :   10 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   33 (  94 expanded)
%              Number of equality atoms :   32 (  93 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f31])).

fof(f31,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(superposition,[],[f30,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) ),
    inference(definition_unfolding,[],[f21,f28])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f22,f26,f27])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f15,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f17,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f18,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f17,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f15,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f16,f25])).

fof(f16,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f30,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f14,f25,f25,f27,f27])).

fof(f14,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:39:29 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.47  % (13222)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.47  % (13220)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.47  % (13220)Refutation found. Thanks to Tanya!
% 0.23/0.47  % SZS status Theorem for theBenchmark
% 0.23/0.48  % (13221)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.48  % (13231)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.23/0.48  % (13232)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.48  % (13230)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.23/0.48  % (13223)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.48  % (13228)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.48  % SZS output start Proof for theBenchmark
% 0.23/0.48  fof(f32,plain,(
% 0.23/0.48    $false),
% 0.23/0.48    inference(trivial_inequality_removal,[],[f31])).
% 0.23/0.48  fof(f31,plain,(
% 0.23/0.48    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.23/0.48    inference(superposition,[],[f30,f29])).
% 0.23/0.48  fof(f29,plain,(
% 0.23/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)))) )),
% 0.23/0.48    inference(definition_unfolding,[],[f21,f28])).
% 0.23/0.48  fof(f28,plain,(
% 0.23/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X6,X6,X6,X6,X6,X6)))) )),
% 0.23/0.48    inference(definition_unfolding,[],[f22,f26,f27])).
% 0.23/0.48  fof(f27,plain,(
% 0.23/0.48    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.23/0.48    inference(definition_unfolding,[],[f15,f25])).
% 0.23/0.48  fof(f25,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.23/0.48    inference(definition_unfolding,[],[f17,f24])).
% 0.23/0.48  fof(f24,plain,(
% 0.23/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.23/0.48    inference(definition_unfolding,[],[f18,f23])).
% 0.23/0.48  fof(f23,plain,(
% 0.23/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.23/0.48    inference(definition_unfolding,[],[f19,f20])).
% 0.23/0.48  fof(f20,plain,(
% 0.23/0.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f6])).
% 0.23/0.48  fof(f6,axiom,(
% 0.23/0.48    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.23/0.48  fof(f19,plain,(
% 0.23/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f5])).
% 0.23/0.48  fof(f5,axiom,(
% 0.23/0.48    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.23/0.48  fof(f18,plain,(
% 0.23/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f4])).
% 0.23/0.48  fof(f4,axiom,(
% 0.23/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.48  fof(f17,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f3])).
% 0.23/0.48  fof(f3,axiom,(
% 0.23/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.48  fof(f15,plain,(
% 0.23/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f2])).
% 0.23/0.48  fof(f2,axiom,(
% 0.23/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.48  fof(f26,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 0.23/0.48    inference(definition_unfolding,[],[f16,f25])).
% 0.23/0.48  fof(f16,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f8])).
% 0.23/0.48  fof(f8,axiom,(
% 0.23/0.48    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.23/0.48  fof(f22,plain,(
% 0.23/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 0.23/0.48    inference(cnf_transformation,[],[f1])).
% 0.23/0.48  fof(f1,axiom,(
% 0.23/0.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).
% 0.23/0.48  fof(f21,plain,(
% 0.23/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f7])).
% 0.23/0.48  fof(f7,axiom,(
% 0.23/0.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.23/0.48  fof(f30,plain,(
% 0.23/0.48    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)))),
% 0.23/0.48    inference(definition_unfolding,[],[f14,f25,f25,f27,f27])).
% 0.23/0.48  fof(f14,plain,(
% 0.23/0.48    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.23/0.48    inference(cnf_transformation,[],[f13])).
% 0.23/0.48  fof(f13,plain,(
% 0.23/0.48    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.23/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 0.23/0.48  fof(f12,plain,(
% 0.23/0.48    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.23/0.48    introduced(choice_axiom,[])).
% 0.23/0.48  fof(f11,plain,(
% 0.23/0.48    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.23/0.48    inference(ennf_transformation,[],[f10])).
% 0.23/0.48  fof(f10,negated_conjecture,(
% 0.23/0.48    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.23/0.48    inference(negated_conjecture,[],[f9])).
% 0.23/0.48  fof(f9,conjecture,(
% 0.23/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 0.23/0.48  % SZS output end Proof for theBenchmark
% 0.23/0.48  % (13220)------------------------------
% 0.23/0.48  % (13220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.48  % (13220)Termination reason: Refutation
% 0.23/0.48  
% 0.23/0.48  % (13220)Memory used [KB]: 6140
% 0.23/0.48  % (13220)Time elapsed: 0.053 s
% 0.23/0.48  % (13220)------------------------------
% 0.23/0.48  % (13220)------------------------------
% 0.23/0.48  % (13229)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.23/0.49  % (13217)Success in time 0.116 s
%------------------------------------------------------------------------------

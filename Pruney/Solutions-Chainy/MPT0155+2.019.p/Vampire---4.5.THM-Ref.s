%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 139 expanded)
%              Number of leaves         :    9 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :   34 ( 140 expanded)
%              Number of equality atoms :   33 ( 139 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f254])).

fof(f254,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(superposition,[],[f38,f192])).

fof(f192,plain,(
    ! [X17,X18,X16] : k1_enumset1(X16,X17,X18) = k5_xboole_0(k1_enumset1(X16,X16,X16),k4_xboole_0(k1_enumset1(X16,X17,X18),k1_enumset1(X16,X16,X16))) ),
    inference(superposition,[],[f51,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0))) ),
    inference(superposition,[],[f42,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f22,f21,f20,f31])).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f19,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X2,X3,X0),k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X0))) = k5_xboole_0(k1_enumset1(X2,X2,X3),k4_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) ),
    inference(superposition,[],[f39,f37])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X2,X2,X2))),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2))) ),
    inference(definition_unfolding,[],[f26,f33,f21])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X2,X2,X2))),k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f25,f21,f20,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0))) ),
    inference(definition_unfolding,[],[f23,f21,f31])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_enumset1)).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(f51,plain,(
    ! [X6,X4,X7,X5,X3] : k5_xboole_0(k1_enumset1(X6,X7,X3),k4_xboole_0(k1_enumset1(X4,X4,X5),k1_enumset1(X6,X7,X3))) = k5_xboole_0(k1_enumset1(X6,X6,X7),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X6,X6,X7))) ),
    inference(forward_demodulation,[],[f50,f37])).

fof(f50,plain,(
    ! [X6,X4,X7,X5,X3] : k5_xboole_0(k1_enumset1(X6,X7,X3),k4_xboole_0(k1_enumset1(X4,X4,X5),k1_enumset1(X6,X7,X3))) = k5_xboole_0(k1_enumset1(X6,X6,X7),k4_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X4),k4_xboole_0(k1_enumset1(X5,X5,X5),k1_enumset1(X3,X3,X4))),k1_enumset1(X6,X6,X7))) ),
    inference(superposition,[],[f39,f42])).

fof(f38,plain,(
    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f18,f32])).

fof(f18,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (13289)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (13284)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (13285)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (13298)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (13286)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (13283)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (13297)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (13284)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (13293)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (13290)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (13300)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (13295)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (13296)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (13291)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (13292)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (13294)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f262,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f254])).
% 0.20/0.49  fof(f254,plain,(
% 0.20/0.49    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)),
% 0.20/0.49    inference(superposition,[],[f38,f192])).
% 0.20/0.49  fof(f192,plain,(
% 0.20/0.49    ( ! [X17,X18,X16] : (k1_enumset1(X16,X17,X18) = k5_xboole_0(k1_enumset1(X16,X16,X16),k4_xboole_0(k1_enumset1(X16,X17,X18),k1_enumset1(X16,X16,X16)))) )),
% 0.20/0.49    inference(superposition,[],[f51,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0)))) )),
% 0.20/0.49    inference(superposition,[],[f42,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f22,f21,f20,f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f19,f20])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X2,X3,X0),k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X0))) = k5_xboole_0(k1_enumset1(X2,X2,X3),k4_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)))) )),
% 0.20/0.49    inference(superposition,[],[f39,f37])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X2,X2,X2))),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f26,f33,f21])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X2,X2,X2))),k1_enumset1(X0,X0,X1)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f25,f21,f20,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f23,f21,f31])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_enumset1)).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X6,X4,X7,X5,X3] : (k5_xboole_0(k1_enumset1(X6,X7,X3),k4_xboole_0(k1_enumset1(X4,X4,X5),k1_enumset1(X6,X7,X3))) = k5_xboole_0(k1_enumset1(X6,X6,X7),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X6,X6,X7)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f50,f37])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X6,X4,X7,X5,X3] : (k5_xboole_0(k1_enumset1(X6,X7,X3),k4_xboole_0(k1_enumset1(X4,X4,X5),k1_enumset1(X6,X7,X3))) = k5_xboole_0(k1_enumset1(X6,X6,X7),k4_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X4),k4_xboole_0(k1_enumset1(X5,X5,X5),k1_enumset1(X3,X3,X4))),k1_enumset1(X6,X6,X7)))) )),
% 0.20/0.49    inference(superposition,[],[f39,f42])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))),
% 0.20/0.49    inference(definition_unfolding,[],[f18,f32])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.49    inference(negated_conjecture,[],[f13])).
% 0.20/0.49  fof(f13,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (13284)------------------------------
% 0.20/0.49  % (13284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (13284)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (13284)Memory used [KB]: 6268
% 0.20/0.49  % (13284)Time elapsed: 0.061 s
% 0.20/0.49  % (13284)------------------------------
% 0.20/0.49  % (13284)------------------------------
% 0.20/0.49  % (13277)Success in time 0.133 s
%------------------------------------------------------------------------------

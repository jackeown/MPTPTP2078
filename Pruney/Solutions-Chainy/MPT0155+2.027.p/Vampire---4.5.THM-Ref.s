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
% DateTime   : Thu Dec  3 12:33:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 199 expanded)
%              Number of leaves         :   11 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :   40 ( 200 expanded)
%              Number of equality atoms :   39 ( 199 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :   11 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
% (5577)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f132,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f131])).

fof(f131,plain,(
    k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) ),
    inference(superposition,[],[f36,f123])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X2,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X3),k3_xboole_0(k2_tarski(X1,X3),k2_tarski(X0,X0)))),k3_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X3),k3_xboole_0(k2_tarski(X1,X3),k2_tarski(X0,X0)))),k2_tarski(X2,X0)))) = k5_xboole_0(k2_tarski(X2,X0),k5_xboole_0(k2_tarski(X1,X3),k3_xboole_0(k2_tarski(X1,X3),k2_tarski(X2,X0)))) ),
    inference(forward_demodulation,[],[f51,f58])).

fof(f58,plain,(
    ! [X14,X15,X13,X16] : k5_xboole_0(k5_xboole_0(k2_tarski(X15,X15),k5_xboole_0(k2_tarski(X13,X14),k3_xboole_0(k2_tarski(X13,X14),k2_tarski(X15,X15)))),k5_xboole_0(k2_tarski(X16,X16),k3_xboole_0(k2_tarski(X16,X16),k5_xboole_0(k2_tarski(X15,X15),k5_xboole_0(k2_tarski(X13,X14),k3_xboole_0(k2_tarski(X13,X14),k2_tarski(X15,X15))))))) = k5_xboole_0(k2_tarski(X15,X13),k5_xboole_0(k2_tarski(X14,X16),k3_xboole_0(k2_tarski(X14,X16),k2_tarski(X15,X13)))) ),
    inference(forward_demodulation,[],[f57,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) ),
    inference(definition_unfolding,[],[f19,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) ),
    inference(definition_unfolding,[],[f22,f29,f18])).

fof(f18,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X14,X15,X13,X16] : k5_xboole_0(k2_tarski(X15,X13),k5_xboole_0(k5_xboole_0(k2_tarski(X14,X14),k5_xboole_0(k2_tarski(X14,X16),k3_xboole_0(k2_tarski(X14,X16),k2_tarski(X14,X14)))),k3_xboole_0(k5_xboole_0(k2_tarski(X14,X14),k5_xboole_0(k2_tarski(X14,X16),k3_xboole_0(k2_tarski(X14,X16),k2_tarski(X14,X14)))),k2_tarski(X15,X13)))) = k5_xboole_0(k5_xboole_0(k2_tarski(X15,X15),k5_xboole_0(k2_tarski(X13,X14),k3_xboole_0(k2_tarski(X13,X14),k2_tarski(X15,X15)))),k5_xboole_0(k2_tarski(X16,X16),k3_xboole_0(k2_tarski(X16,X16),k5_xboole_0(k2_tarski(X15,X15),k5_xboole_0(k2_tarski(X13,X14),k3_xboole_0(k2_tarski(X13,X14),k2_tarski(X15,X15))))))) ),
    inference(forward_demodulation,[],[f54,f35])).

fof(f54,plain,(
    ! [X14,X15,X13,X16] : k5_xboole_0(k2_tarski(X15,X13),k5_xboole_0(k5_xboole_0(k2_tarski(X14,X14),k5_xboole_0(k2_tarski(X14,X16),k3_xboole_0(k2_tarski(X14,X16),k2_tarski(X14,X14)))),k3_xboole_0(k5_xboole_0(k2_tarski(X14,X14),k5_xboole_0(k2_tarski(X14,X16),k3_xboole_0(k2_tarski(X14,X16),k2_tarski(X14,X14)))),k2_tarski(X15,X13)))) = k5_xboole_0(k5_xboole_0(k2_tarski(X15,X15),k5_xboole_0(k5_xboole_0(k2_tarski(X13,X13),k5_xboole_0(k2_tarski(X13,X14),k3_xboole_0(k2_tarski(X13,X14),k2_tarski(X13,X13)))),k3_xboole_0(k5_xboole_0(k2_tarski(X13,X13),k5_xboole_0(k2_tarski(X13,X14),k3_xboole_0(k2_tarski(X13,X14),k2_tarski(X13,X13)))),k2_tarski(X15,X15)))),k5_xboole_0(k2_tarski(X16,X16),k3_xboole_0(k2_tarski(X16,X16),k5_xboole_0(k2_tarski(X15,X15),k5_xboole_0(k5_xboole_0(k2_tarski(X13,X13),k5_xboole_0(k2_tarski(X13,X14),k3_xboole_0(k2_tarski(X13,X14),k2_tarski(X13,X13)))),k3_xboole_0(k5_xboole_0(k2_tarski(X13,X13),k5_xboole_0(k2_tarski(X13,X14),k3_xboole_0(k2_tarski(X13,X14),k2_tarski(X13,X13)))),k2_tarski(X15,X15))))))) ),
    inference(superposition,[],[f38,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f23,f30,f29,f18])).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k2_tarski(X0,X1)))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0)))),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0))))))) ),
    inference(definition_unfolding,[],[f26,f32,f29,f31,f18])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0)))) ),
    inference(definition_unfolding,[],[f24,f29,f18,f30])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f25,f29,f30])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

% (5588)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f51,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X2,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X3),k3_xboole_0(k2_tarski(X1,X3),k2_tarski(X0,X0)))),k3_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X3),k3_xboole_0(k2_tarski(X1,X3),k2_tarski(X0,X0)))),k2_tarski(X2,X0)))) = k5_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X2)))),k5_xboole_0(k2_tarski(X3,X3),k3_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X2))))))) ),
    inference(superposition,[],[f38,f35])).

fof(f36,plain,(
    k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0)))) ),
    inference(definition_unfolding,[],[f17,f30,f31])).

fof(f17,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:58:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (5578)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (5580)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (5578)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (5586)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (5591)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (5585)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (5583)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  % (5577)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f131])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0))))),
% 0.21/0.48    inference(superposition,[],[f36,f123])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X2,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X3),k3_xboole_0(k2_tarski(X1,X3),k2_tarski(X0,X0)))),k3_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X3),k3_xboole_0(k2_tarski(X1,X3),k2_tarski(X0,X0)))),k2_tarski(X2,X0)))) = k5_xboole_0(k2_tarski(X2,X0),k5_xboole_0(k2_tarski(X1,X3),k3_xboole_0(k2_tarski(X1,X3),k2_tarski(X2,X0))))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f51,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X14,X15,X13,X16] : (k5_xboole_0(k5_xboole_0(k2_tarski(X15,X15),k5_xboole_0(k2_tarski(X13,X14),k3_xboole_0(k2_tarski(X13,X14),k2_tarski(X15,X15)))),k5_xboole_0(k2_tarski(X16,X16),k3_xboole_0(k2_tarski(X16,X16),k5_xboole_0(k2_tarski(X15,X15),k5_xboole_0(k2_tarski(X13,X14),k3_xboole_0(k2_tarski(X13,X14),k2_tarski(X15,X15))))))) = k5_xboole_0(k2_tarski(X15,X13),k5_xboole_0(k2_tarski(X14,X16),k3_xboole_0(k2_tarski(X14,X16),k2_tarski(X15,X13))))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f57,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f19,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f22,f29,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f21,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X14,X15,X13,X16] : (k5_xboole_0(k2_tarski(X15,X13),k5_xboole_0(k5_xboole_0(k2_tarski(X14,X14),k5_xboole_0(k2_tarski(X14,X16),k3_xboole_0(k2_tarski(X14,X16),k2_tarski(X14,X14)))),k3_xboole_0(k5_xboole_0(k2_tarski(X14,X14),k5_xboole_0(k2_tarski(X14,X16),k3_xboole_0(k2_tarski(X14,X16),k2_tarski(X14,X14)))),k2_tarski(X15,X13)))) = k5_xboole_0(k5_xboole_0(k2_tarski(X15,X15),k5_xboole_0(k2_tarski(X13,X14),k3_xboole_0(k2_tarski(X13,X14),k2_tarski(X15,X15)))),k5_xboole_0(k2_tarski(X16,X16),k3_xboole_0(k2_tarski(X16,X16),k5_xboole_0(k2_tarski(X15,X15),k5_xboole_0(k2_tarski(X13,X14),k3_xboole_0(k2_tarski(X13,X14),k2_tarski(X15,X15)))))))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f54,f35])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X14,X15,X13,X16] : (k5_xboole_0(k2_tarski(X15,X13),k5_xboole_0(k5_xboole_0(k2_tarski(X14,X14),k5_xboole_0(k2_tarski(X14,X16),k3_xboole_0(k2_tarski(X14,X16),k2_tarski(X14,X14)))),k3_xboole_0(k5_xboole_0(k2_tarski(X14,X14),k5_xboole_0(k2_tarski(X14,X16),k3_xboole_0(k2_tarski(X14,X16),k2_tarski(X14,X14)))),k2_tarski(X15,X13)))) = k5_xboole_0(k5_xboole_0(k2_tarski(X15,X15),k5_xboole_0(k5_xboole_0(k2_tarski(X13,X13),k5_xboole_0(k2_tarski(X13,X14),k3_xboole_0(k2_tarski(X13,X14),k2_tarski(X13,X13)))),k3_xboole_0(k5_xboole_0(k2_tarski(X13,X13),k5_xboole_0(k2_tarski(X13,X14),k3_xboole_0(k2_tarski(X13,X14),k2_tarski(X13,X13)))),k2_tarski(X15,X15)))),k5_xboole_0(k2_tarski(X16,X16),k3_xboole_0(k2_tarski(X16,X16),k5_xboole_0(k2_tarski(X15,X15),k5_xboole_0(k5_xboole_0(k2_tarski(X13,X13),k5_xboole_0(k2_tarski(X13,X14),k3_xboole_0(k2_tarski(X13,X14),k2_tarski(X13,X13)))),k3_xboole_0(k5_xboole_0(k2_tarski(X13,X13),k5_xboole_0(k2_tarski(X13,X14),k3_xboole_0(k2_tarski(X13,X14),k2_tarski(X13,X13)))),k2_tarski(X15,X15)))))))) )),
% 0.21/0.48    inference(superposition,[],[f38,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1))))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f23,f30,f29,f18])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k2_tarski(X0,X1)))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0)))),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0)))))))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f26,f32,f29,f31,f18])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0))))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f24,f29,f18,f30])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k2_tarski(X0,X1))))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f25,f29,f30])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 0.21/0.48  % (5588)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X2,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X3),k3_xboole_0(k2_tarski(X1,X3),k2_tarski(X0,X0)))),k3_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X3),k3_xboole_0(k2_tarski(X1,X3),k2_tarski(X0,X0)))),k2_tarski(X2,X0)))) = k5_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X2)))),k5_xboole_0(k2_tarski(X3,X3),k3_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X2)))))))) )),
% 0.21/0.48    inference(superposition,[],[f38,f35])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0))))),
% 0.21/0.48    inference(definition_unfolding,[],[f17,f30,f31])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.48    inference(negated_conjecture,[],[f12])).
% 0.21/0.48  fof(f12,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (5578)------------------------------
% 0.21/0.48  % (5578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (5578)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (5578)Memory used [KB]: 6268
% 0.21/0.48  % (5578)Time elapsed: 0.060 s
% 0.21/0.48  % (5578)------------------------------
% 0.21/0.48  % (5578)------------------------------
% 0.21/0.48  % (5584)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (5572)Success in time 0.12 s
%------------------------------------------------------------------------------

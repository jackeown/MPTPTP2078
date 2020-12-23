%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:58 EST 2020

% Result     : Theorem 3.44s
% Output     : Refutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 126 expanded)
%              Number of leaves         :   14 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :   62 ( 127 expanded)
%              Number of equality atoms :   61 ( 126 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7088,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7087,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f7087,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4)) ),
    inference(forward_demodulation,[],[f7086,f108])).

fof(f108,plain,(
    ! [X8,X7,X9] : k2_tarski(k4_tarski(X7,X8),k4_tarski(X9,X8)) = k2_zfmisc_1(k2_tarski(X7,X9),k1_tarski(X8)) ),
    inference(forward_demodulation,[],[f107,f20])).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f107,plain,(
    ! [X8,X7,X9] : k2_zfmisc_1(k2_tarski(X7,X9),k2_tarski(X8,X8)) = k2_tarski(k4_tarski(X7,X8),k4_tarski(X9,X8)) ),
    inference(forward_demodulation,[],[f99,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f99,plain,(
    ! [X8,X7,X9] : k2_zfmisc_1(k2_tarski(X7,X9),k2_tarski(X8,X8)) = k1_enumset1(k4_tarski(X7,X8),k4_tarski(X7,X8),k4_tarski(X9,X8)) ),
    inference(superposition,[],[f54,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X1,X2,X0,X0) = k1_enumset1(X1,X2,X0) ),
    inference(forward_demodulation,[],[f48,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) ),
    inference(superposition,[],[f28,f20])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f7086,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f6861,f289])).

fof(f289,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5)) ),
    inference(forward_demodulation,[],[f279,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f279,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5)) ),
    inference(superposition,[],[f83,f24])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f75,f24])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(superposition,[],[f30,f24])).

fof(f6861,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(superposition,[],[f19,f6701])).

fof(f6701,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7) ),
    inference(superposition,[],[f421,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(backward_demodulation,[],[f58,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(forward_demodulation,[],[f65,f28])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(superposition,[],[f32,f21])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(superposition,[],[f31,f20])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(f421,plain,(
    ! [X4,X2,X5,X3] : k2_enumset1(X5,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k1_enumset1(X3,X2,X4)) ),
    inference(superposition,[],[f68,f370])).

fof(f370,plain,(
    ! [X12,X13,X11] : k1_enumset1(X11,X12,X13) = k1_enumset1(X12,X11,X13) ),
    inference(superposition,[],[f129,f96])).

fof(f96,plain,(
    ! [X10,X11,X9] : k2_enumset1(X9,X10,X9,X11) = k1_enumset1(X9,X10,X11) ),
    inference(forward_demodulation,[],[f93,f26])).

fof(f93,plain,(
    ! [X10,X11,X9] : k2_enumset1(X9,X10,X9,X11) = k2_xboole_0(k2_tarski(X9,X10),k1_tarski(X11)) ),
    inference(superposition,[],[f29,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(forward_demodulation,[],[f70,f21])).

fof(f70,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f49,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X1,X0,X2) = k2_enumset1(X0,X1,X2,X1) ),
    inference(superposition,[],[f28,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f129,plain,(
    ! [X10,X11,X9] : k2_enumset1(X9,X10,X9,X11) = k1_enumset1(X10,X9,X11) ),
    inference(forward_demodulation,[],[f125,f26])).

fof(f125,plain,(
    ! [X10,X11,X9] : k2_enumset1(X9,X10,X9,X11) = k2_xboole_0(k2_tarski(X10,X9),k1_tarski(X11)) ),
    inference(superposition,[],[f29,f106])).

fof(f106,plain,(
    ! [X2,X3] : k2_tarski(X2,X3) = k1_enumset1(X3,X2,X3) ),
    inference(forward_demodulation,[],[f98,f103])).

fof(f103,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X1) ),
    inference(forward_demodulation,[],[f97,f21])).

fof(f97,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X0,X1,X1) ),
    inference(superposition,[],[f54,f25])).

fof(f98,plain,(
    ! [X2,X3] : k1_enumset1(X3,X2,X3) = k1_enumset1(X2,X3,X3) ),
    inference(superposition,[],[f54,f49])).

fof(f19,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:42:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (24423)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (24430)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.51  % (24420)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.52  % (24434)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.52  % (24421)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.52  % (24435)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.52  % (24425)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.52  % (24436)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.52  % (24426)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (24428)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.53  % (24422)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.53  % (24429)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.53  % (24438)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.53  % (24424)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.54  % (24432)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.54  % (24432)Refutation not found, incomplete strategy% (24432)------------------------------
% 0.22/0.54  % (24432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24432)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (24432)Memory used [KB]: 10618
% 0.22/0.54  % (24432)Time elapsed: 0.111 s
% 0.22/0.54  % (24432)------------------------------
% 0.22/0.54  % (24432)------------------------------
% 0.22/0.54  % (24433)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.55  % (24427)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.56  % (24437)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 3.44/0.84  % (24423)Refutation found. Thanks to Tanya!
% 3.44/0.84  % SZS status Theorem for theBenchmark
% 3.44/0.84  % SZS output start Proof for theBenchmark
% 3.44/0.84  fof(f7088,plain,(
% 3.44/0.84    $false),
% 3.44/0.84    inference(subsumption_resolution,[],[f7087,f23])).
% 3.44/0.84  fof(f23,plain,(
% 3.44/0.84    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 3.44/0.84    inference(cnf_transformation,[],[f13])).
% 3.44/0.84  fof(f13,axiom,(
% 3.44/0.84    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 3.44/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 3.44/0.84  fof(f7087,plain,(
% 3.44/0.84    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4))),
% 3.44/0.84    inference(forward_demodulation,[],[f7086,f108])).
% 3.44/0.84  fof(f108,plain,(
% 3.44/0.84    ( ! [X8,X7,X9] : (k2_tarski(k4_tarski(X7,X8),k4_tarski(X9,X8)) = k2_zfmisc_1(k2_tarski(X7,X9),k1_tarski(X8))) )),
% 3.44/0.84    inference(forward_demodulation,[],[f107,f20])).
% 3.44/0.84  fof(f20,plain,(
% 3.44/0.84    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.44/0.84    inference(cnf_transformation,[],[f7])).
% 3.44/0.84  fof(f7,axiom,(
% 3.44/0.84    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.44/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 3.44/0.84  fof(f107,plain,(
% 3.44/0.84    ( ! [X8,X7,X9] : (k2_zfmisc_1(k2_tarski(X7,X9),k2_tarski(X8,X8)) = k2_tarski(k4_tarski(X7,X8),k4_tarski(X9,X8))) )),
% 3.44/0.84    inference(forward_demodulation,[],[f99,f21])).
% 3.44/0.84  fof(f21,plain,(
% 3.44/0.84    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.44/0.84    inference(cnf_transformation,[],[f8])).
% 3.44/0.84  fof(f8,axiom,(
% 3.44/0.84    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.44/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.44/0.84  fof(f99,plain,(
% 3.44/0.84    ( ! [X8,X7,X9] : (k2_zfmisc_1(k2_tarski(X7,X9),k2_tarski(X8,X8)) = k1_enumset1(k4_tarski(X7,X8),k4_tarski(X7,X8),k4_tarski(X9,X8))) )),
% 3.44/0.84    inference(superposition,[],[f54,f30])).
% 3.44/0.84  fof(f30,plain,(
% 3.44/0.84    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 3.44/0.84    inference(cnf_transformation,[],[f11])).
% 3.44/0.84  fof(f11,axiom,(
% 3.44/0.84    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 3.44/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 3.44/0.84  fof(f54,plain,(
% 3.44/0.84    ( ! [X2,X0,X1] : (k2_enumset1(X1,X2,X0,X0) = k1_enumset1(X1,X2,X0)) )),
% 3.44/0.84    inference(forward_demodulation,[],[f48,f26])).
% 3.44/0.84  fof(f26,plain,(
% 3.44/0.84    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 3.44/0.84    inference(cnf_transformation,[],[f4])).
% 3.44/0.84  fof(f4,axiom,(
% 3.44/0.84    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 3.44/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 3.44/0.84  fof(f48,plain,(
% 3.44/0.84    ( ! [X2,X0,X1] : (k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) )),
% 3.44/0.84    inference(superposition,[],[f28,f20])).
% 3.44/0.84  fof(f28,plain,(
% 3.44/0.84    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 3.44/0.84    inference(cnf_transformation,[],[f1])).
% 3.44/0.84  fof(f1,axiom,(
% 3.44/0.84    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 3.44/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 3.44/0.84  fof(f7086,plain,(
% 3.44/0.84    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK4))),
% 3.44/0.84    inference(superposition,[],[f6861,f289])).
% 3.44/0.84  fof(f289,plain,(
% 3.44/0.84    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5))) )),
% 3.44/0.84    inference(forward_demodulation,[],[f279,f24])).
% 3.44/0.84  fof(f24,plain,(
% 3.44/0.84    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 3.44/0.84    inference(cnf_transformation,[],[f12])).
% 3.44/0.84  fof(f12,axiom,(
% 3.44/0.84    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 3.44/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 3.44/0.84  fof(f279,plain,(
% 3.44/0.84    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5))) )),
% 3.44/0.84    inference(superposition,[],[f83,f24])).
% 3.44/0.84  fof(f83,plain,(
% 3.44/0.84    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 3.44/0.84    inference(forward_demodulation,[],[f75,f24])).
% 3.44/0.84  fof(f75,plain,(
% 3.44/0.84    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 3.44/0.84    inference(superposition,[],[f30,f24])).
% 3.44/0.84  fof(f6861,plain,(
% 3.44/0.84    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4))),
% 3.44/0.84    inference(superposition,[],[f19,f6701])).
% 3.44/0.84  fof(f6701,plain,(
% 3.44/0.84    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7)) )),
% 3.44/0.84    inference(superposition,[],[f421,f68])).
% 3.44/0.84  fof(f68,plain,(
% 3.44/0.84    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 3.44/0.84    inference(backward_demodulation,[],[f58,f67])).
% 3.44/0.84  fof(f67,plain,(
% 3.44/0.84    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.44/0.84    inference(forward_demodulation,[],[f65,f28])).
% 3.44/0.84  fof(f65,plain,(
% 3.44/0.84    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.44/0.84    inference(superposition,[],[f32,f21])).
% 3.44/0.85  fof(f32,plain,(
% 3.44/0.85    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 3.44/0.85    inference(cnf_transformation,[],[f2])).
% 3.44/0.85  fof(f2,axiom,(
% 3.44/0.85    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 3.44/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).
% 3.44/0.85  fof(f58,plain,(
% 3.44/0.85    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 3.44/0.85    inference(superposition,[],[f31,f20])).
% 3.44/0.85  fof(f31,plain,(
% 3.44/0.85    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 3.44/0.85    inference(cnf_transformation,[],[f6])).
% 3.44/0.85  fof(f6,axiom,(
% 3.44/0.85    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 3.44/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).
% 3.44/0.85  fof(f421,plain,(
% 3.44/0.85    ( ! [X4,X2,X5,X3] : (k2_enumset1(X5,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k1_enumset1(X3,X2,X4))) )),
% 3.44/0.85    inference(superposition,[],[f68,f370])).
% 3.44/0.85  fof(f370,plain,(
% 3.44/0.85    ( ! [X12,X13,X11] : (k1_enumset1(X11,X12,X13) = k1_enumset1(X12,X11,X13)) )),
% 3.44/0.85    inference(superposition,[],[f129,f96])).
% 3.44/0.85  fof(f96,plain,(
% 3.44/0.85    ( ! [X10,X11,X9] : (k2_enumset1(X9,X10,X9,X11) = k1_enumset1(X9,X10,X11)) )),
% 3.44/0.85    inference(forward_demodulation,[],[f93,f26])).
% 3.44/0.85  fof(f93,plain,(
% 3.44/0.85    ( ! [X10,X11,X9] : (k2_enumset1(X9,X10,X9,X11) = k2_xboole_0(k2_tarski(X9,X10),k1_tarski(X11))) )),
% 3.44/0.85    inference(superposition,[],[f29,f72])).
% 3.44/0.85  fof(f72,plain,(
% 3.44/0.85    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 3.44/0.85    inference(forward_demodulation,[],[f70,f21])).
% 3.44/0.85  fof(f70,plain,(
% 3.44/0.85    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 3.44/0.85    inference(superposition,[],[f49,f25])).
% 3.44/0.85  fof(f25,plain,(
% 3.44/0.85    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.44/0.85    inference(cnf_transformation,[],[f9])).
% 3.44/0.85  fof(f9,axiom,(
% 3.44/0.85    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.44/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 3.44/0.85  fof(f49,plain,(
% 3.44/0.85    ( ! [X2,X0,X1] : (k1_enumset1(X1,X0,X2) = k2_enumset1(X0,X1,X2,X1)) )),
% 3.44/0.85    inference(superposition,[],[f28,f27])).
% 3.44/0.85  fof(f27,plain,(
% 3.44/0.85    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))) )),
% 3.44/0.85    inference(cnf_transformation,[],[f3])).
% 3.44/0.85  fof(f3,axiom,(
% 3.44/0.85    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 3.44/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 3.44/0.85  fof(f29,plain,(
% 3.44/0.85    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 3.44/0.85    inference(cnf_transformation,[],[f5])).
% 3.44/0.85  fof(f5,axiom,(
% 3.44/0.85    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 3.44/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 3.44/0.85  fof(f129,plain,(
% 3.44/0.85    ( ! [X10,X11,X9] : (k2_enumset1(X9,X10,X9,X11) = k1_enumset1(X10,X9,X11)) )),
% 3.44/0.85    inference(forward_demodulation,[],[f125,f26])).
% 3.44/0.85  fof(f125,plain,(
% 3.44/0.85    ( ! [X10,X11,X9] : (k2_enumset1(X9,X10,X9,X11) = k2_xboole_0(k2_tarski(X10,X9),k1_tarski(X11))) )),
% 3.44/0.85    inference(superposition,[],[f29,f106])).
% 3.44/0.85  fof(f106,plain,(
% 3.44/0.85    ( ! [X2,X3] : (k2_tarski(X2,X3) = k1_enumset1(X3,X2,X3)) )),
% 3.44/0.85    inference(forward_demodulation,[],[f98,f103])).
% 3.44/0.85  fof(f103,plain,(
% 3.44/0.85    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X1)) )),
% 3.44/0.85    inference(forward_demodulation,[],[f97,f21])).
% 3.44/0.85  fof(f97,plain,(
% 3.44/0.85    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X0,X1,X1)) )),
% 3.44/0.85    inference(superposition,[],[f54,f25])).
% 3.44/0.85  fof(f98,plain,(
% 3.44/0.85    ( ! [X2,X3] : (k1_enumset1(X3,X2,X3) = k1_enumset1(X2,X3,X3)) )),
% 3.44/0.85    inference(superposition,[],[f54,f49])).
% 3.44/0.85  fof(f19,plain,(
% 3.44/0.85    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 3.44/0.85    inference(cnf_transformation,[],[f18])).
% 3.44/0.85  fof(f18,plain,(
% 3.44/0.85    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 3.44/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).
% 3.44/0.85  fof(f17,plain,(
% 3.44/0.85    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 3.44/0.85    introduced(choice_axiom,[])).
% 3.44/0.85  fof(f16,plain,(
% 3.44/0.85    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 3.44/0.85    inference(ennf_transformation,[],[f15])).
% 3.44/0.85  fof(f15,negated_conjecture,(
% 3.44/0.85    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 3.44/0.85    inference(negated_conjecture,[],[f14])).
% 3.44/0.85  fof(f14,conjecture,(
% 3.44/0.85    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 3.44/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
% 3.44/0.85  % SZS output end Proof for theBenchmark
% 3.44/0.85  % (24423)------------------------------
% 3.44/0.85  % (24423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.44/0.85  % (24423)Termination reason: Refutation
% 3.44/0.85  
% 3.44/0.85  % (24423)Memory used [KB]: 7803
% 3.44/0.85  % (24423)Time elapsed: 0.429 s
% 3.44/0.85  % (24423)------------------------------
% 3.44/0.85  % (24423)------------------------------
% 3.44/0.85  % (24415)Success in time 0.485 s
%------------------------------------------------------------------------------

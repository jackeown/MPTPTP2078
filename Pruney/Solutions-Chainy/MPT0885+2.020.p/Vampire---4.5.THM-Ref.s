%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:03 EST 2020

% Result     : Theorem 26.74s
% Output     : Refutation 26.74s
% Verified   : 
% Statistics : Number of formulae       :   59 (  87 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :   15
%              Number of atoms          :   61 (  89 expanded)
%              Number of equality atoms :   60 (  88 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35617,plain,(
    $false ),
    inference(subsumption_resolution,[],[f35616,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f35616,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(forward_demodulation,[],[f35460,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f35460,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f4389,f1715])).

fof(f1715,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5)) ),
    inference(forward_demodulation,[],[f1696,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f1696,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5)) ),
    inference(superposition,[],[f145,f25])).

fof(f145,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f134,f25])).

fof(f134,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(superposition,[],[f33,f25])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f4389,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(superposition,[],[f20,f4288])).

fof(f4288,plain,(
    ! [X14,X12,X13,X11] : k2_enumset1(X11,X12,X13,X14) = k2_enumset1(X11,X13,X12,X14) ),
    inference(superposition,[],[f674,f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X2,X3,X0,X0,X1) = k2_enumset1(X2,X3,X0,X1) ),
    inference(forward_demodulation,[],[f111,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f111,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X2,X3,X0,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f34,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f674,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X6,X6,X7) = k2_enumset1(X4,X6,X5,X7) ),
    inference(forward_demodulation,[],[f662,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f662,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X6,X6,X7) = k2_xboole_0(k1_enumset1(X4,X6,X5),k1_tarski(X7)) ),
    inference(superposition,[],[f35,f303])).

fof(f303,plain,(
    ! [X10,X11,X9] : k2_enumset1(X11,X9,X10,X10) = k1_enumset1(X11,X10,X9) ),
    inference(forward_demodulation,[],[f294,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(forward_demodulation,[],[f50,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(superposition,[],[f31,f21])).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f294,plain,(
    ! [X10,X11,X9] : k2_enumset1(X11,X9,X10,X10) = k2_xboole_0(k1_tarski(X11),k2_tarski(X10,X9)) ),
    inference(superposition,[],[f120,f173])).

fof(f173,plain,(
    ! [X0,X1] : k2_tarski(X1,X0) = k1_enumset1(X0,X1,X1) ),
    inference(superposition,[],[f106,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f106,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X1,X0),k1_tarski(X0)) ),
    inference(backward_demodulation,[],[f42,f105])).

fof(f105,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(forward_demodulation,[],[f103,f22])).

fof(f103,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f52,f26])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X1,X0,X2) = k2_enumset1(X0,X1,X2,X1) ),
    inference(superposition,[],[f31,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X1,X0) = k2_xboole_0(k2_tarski(X1,X0),k1_tarski(X0)) ),
    inference(superposition,[],[f28,f21])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(backward_demodulation,[],[f108,f119])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(forward_demodulation,[],[f117,f32])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(superposition,[],[f35,f26])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(superposition,[],[f34,f21])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f20,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))
   => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:01:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (7436)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (7437)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (7443)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (7441)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (7443)Refutation not found, incomplete strategy% (7443)------------------------------
% 0.21/0.48  % (7443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (7434)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (7443)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (7443)Memory used [KB]: 10618
% 0.21/0.48  % (7443)Time elapsed: 0.053 s
% 0.21/0.48  % (7443)------------------------------
% 0.21/0.48  % (7443)------------------------------
% 0.21/0.48  % (7432)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (7433)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (7445)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (7446)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (7431)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (7435)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (7440)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (7449)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.52  % (7447)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.52  % (7442)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (7439)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.53  % (7444)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.54  % (7448)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 5.14/1.02  % (7435)Time limit reached!
% 5.14/1.02  % (7435)------------------------------
% 5.14/1.02  % (7435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.14/1.02  % (7435)Termination reason: Time limit
% 5.14/1.02  % (7435)Termination phase: Saturation
% 5.14/1.02  
% 5.14/1.02  % (7435)Memory used [KB]: 11257
% 5.14/1.02  % (7435)Time elapsed: 0.600 s
% 5.14/1.02  % (7435)------------------------------
% 5.14/1.02  % (7435)------------------------------
% 12.47/1.94  % (7436)Time limit reached!
% 12.47/1.94  % (7436)------------------------------
% 12.47/1.94  % (7436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.47/1.94  % (7436)Termination reason: Time limit
% 12.47/1.94  % (7436)Termination phase: Saturation
% 12.47/1.94  
% 12.47/1.94  % (7436)Memory used [KB]: 31854
% 12.47/1.94  % (7436)Time elapsed: 1.500 s
% 12.47/1.94  % (7436)------------------------------
% 12.47/1.94  % (7436)------------------------------
% 12.47/1.94  % (7437)Time limit reached!
% 12.47/1.94  % (7437)------------------------------
% 12.47/1.94  % (7437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.47/1.94  % (7437)Termination reason: Time limit
% 12.47/1.94  % (7437)Termination phase: Saturation
% 12.47/1.94  
% 12.47/1.94  % (7437)Memory used [KB]: 22899
% 12.47/1.94  % (7437)Time elapsed: 1.500 s
% 12.47/1.94  % (7437)------------------------------
% 12.47/1.94  % (7437)------------------------------
% 14.90/2.27  % (7433)Time limit reached!
% 14.90/2.27  % (7433)------------------------------
% 14.90/2.27  % (7433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.90/2.27  % (7433)Termination reason: Time limit
% 14.90/2.27  % (7433)Termination phase: Saturation
% 14.90/2.27  
% 14.90/2.27  % (7433)Memory used [KB]: 15991
% 14.90/2.27  % (7433)Time elapsed: 1.800 s
% 14.90/2.27  % (7433)------------------------------
% 14.90/2.27  % (7433)------------------------------
% 17.79/2.62  % (7444)Time limit reached!
% 17.79/2.62  % (7444)------------------------------
% 17.79/2.62  % (7444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.79/2.62  % (7444)Termination reason: Time limit
% 17.79/2.62  % (7444)Termination phase: Saturation
% 17.79/2.62  
% 17.79/2.62  % (7444)Memory used [KB]: 12409
% 17.79/2.62  % (7444)Time elapsed: 2.200 s
% 17.79/2.62  % (7444)------------------------------
% 17.79/2.62  % (7444)------------------------------
% 26.74/3.72  % (7434)Refutation found. Thanks to Tanya!
% 26.74/3.72  % SZS status Theorem for theBenchmark
% 26.74/3.72  % SZS output start Proof for theBenchmark
% 26.74/3.72  fof(f35617,plain,(
% 26.74/3.72    $false),
% 26.74/3.72    inference(subsumption_resolution,[],[f35616,f24])).
% 26.74/3.72  fof(f24,plain,(
% 26.74/3.72    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 26.74/3.72    inference(cnf_transformation,[],[f14])).
% 26.74/3.72  fof(f14,axiom,(
% 26.74/3.72    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 26.74/3.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 26.74/3.72  fof(f35616,plain,(
% 26.74/3.72    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4))),
% 26.74/3.72    inference(forward_demodulation,[],[f35460,f29])).
% 26.74/3.72  fof(f29,plain,(
% 26.74/3.72    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 26.74/3.72    inference(cnf_transformation,[],[f12])).
% 26.74/3.72  fof(f12,axiom,(
% 26.74/3.72    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 26.74/3.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 26.74/3.72  fof(f35460,plain,(
% 26.74/3.72    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4))),
% 26.74/3.72    inference(superposition,[],[f4389,f1715])).
% 26.74/3.72  fof(f1715,plain,(
% 26.74/3.72    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5))) )),
% 26.74/3.72    inference(forward_demodulation,[],[f1696,f25])).
% 26.74/3.72  fof(f25,plain,(
% 26.74/3.72    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 26.74/3.72    inference(cnf_transformation,[],[f13])).
% 26.74/3.72  fof(f13,axiom,(
% 26.74/3.72    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 26.74/3.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 26.74/3.72  fof(f1696,plain,(
% 26.74/3.72    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5))) )),
% 26.74/3.72    inference(superposition,[],[f145,f25])).
% 26.74/3.72  fof(f145,plain,(
% 26.74/3.72    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 26.74/3.72    inference(forward_demodulation,[],[f134,f25])).
% 26.74/3.72  fof(f134,plain,(
% 26.74/3.72    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 26.74/3.72    inference(superposition,[],[f33,f25])).
% 26.74/3.72  fof(f33,plain,(
% 26.74/3.72    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 26.74/3.72    inference(cnf_transformation,[],[f11])).
% 26.74/3.72  fof(f11,axiom,(
% 26.74/3.72    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 26.74/3.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 26.74/3.72  fof(f4389,plain,(
% 26.74/3.72    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4))),
% 26.74/3.72    inference(superposition,[],[f20,f4288])).
% 26.74/3.72  fof(f4288,plain,(
% 26.74/3.72    ( ! [X14,X12,X13,X11] : (k2_enumset1(X11,X12,X13,X14) = k2_enumset1(X11,X13,X12,X14)) )),
% 26.74/3.72    inference(superposition,[],[f674,f112])).
% 26.74/3.72  fof(f112,plain,(
% 26.74/3.72    ( ! [X2,X0,X3,X1] : (k3_enumset1(X2,X3,X0,X0,X1) = k2_enumset1(X2,X3,X0,X1)) )),
% 26.74/3.72    inference(forward_demodulation,[],[f111,f31])).
% 26.74/3.72  fof(f31,plain,(
% 26.74/3.72    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 26.74/3.72    inference(cnf_transformation,[],[f1])).
% 26.74/3.72  fof(f1,axiom,(
% 26.74/3.72    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 26.74/3.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 26.74/3.72  fof(f111,plain,(
% 26.74/3.72    ( ! [X2,X0,X3,X1] : (k3_enumset1(X2,X3,X0,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) )),
% 26.74/3.72    inference(superposition,[],[f34,f22])).
% 26.74/3.72  fof(f22,plain,(
% 26.74/3.72    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 26.74/3.72    inference(cnf_transformation,[],[f8])).
% 26.74/3.72  fof(f8,axiom,(
% 26.74/3.72    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 26.74/3.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 26.74/3.72  fof(f34,plain,(
% 26.74/3.72    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 26.74/3.72    inference(cnf_transformation,[],[f5])).
% 26.74/3.72  fof(f5,axiom,(
% 26.74/3.72    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 26.74/3.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 26.74/3.72  fof(f674,plain,(
% 26.74/3.72    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X6,X6,X7) = k2_enumset1(X4,X6,X5,X7)) )),
% 26.74/3.72    inference(forward_demodulation,[],[f662,f32])).
% 26.74/3.72  fof(f32,plain,(
% 26.74/3.72    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 26.74/3.72    inference(cnf_transformation,[],[f4])).
% 26.74/3.72  fof(f4,axiom,(
% 26.74/3.72    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 26.74/3.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 26.74/3.72  fof(f662,plain,(
% 26.74/3.72    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X6,X6,X7) = k2_xboole_0(k1_enumset1(X4,X6,X5),k1_tarski(X7))) )),
% 26.74/3.72    inference(superposition,[],[f35,f303])).
% 26.74/3.72  fof(f303,plain,(
% 26.74/3.72    ( ! [X10,X11,X9] : (k2_enumset1(X11,X9,X10,X10) = k1_enumset1(X11,X10,X9)) )),
% 26.74/3.72    inference(forward_demodulation,[],[f294,f56])).
% 26.74/3.72  fof(f56,plain,(
% 26.74/3.72    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 26.74/3.72    inference(forward_demodulation,[],[f50,f26])).
% 26.74/3.72  fof(f26,plain,(
% 26.74/3.72    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 26.74/3.72    inference(cnf_transformation,[],[f9])).
% 26.74/3.72  fof(f9,axiom,(
% 26.74/3.72    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 26.74/3.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 26.74/3.72  fof(f50,plain,(
% 26.74/3.72    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 26.74/3.72    inference(superposition,[],[f31,f21])).
% 26.74/3.72  fof(f21,plain,(
% 26.74/3.72    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 26.74/3.72    inference(cnf_transformation,[],[f7])).
% 26.74/3.72  fof(f7,axiom,(
% 26.74/3.72    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 26.74/3.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 26.74/3.72  fof(f294,plain,(
% 26.74/3.72    ( ! [X10,X11,X9] : (k2_enumset1(X11,X9,X10,X10) = k2_xboole_0(k1_tarski(X11),k2_tarski(X10,X9))) )),
% 26.74/3.72    inference(superposition,[],[f120,f173])).
% 26.74/3.72  fof(f173,plain,(
% 26.74/3.72    ( ! [X0,X1] : (k2_tarski(X1,X0) = k1_enumset1(X0,X1,X1)) )),
% 26.74/3.72    inference(superposition,[],[f106,f27])).
% 26.74/3.72  fof(f27,plain,(
% 26.74/3.72    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 26.74/3.72    inference(cnf_transformation,[],[f3])).
% 26.74/3.72  fof(f3,axiom,(
% 26.74/3.72    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 26.74/3.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 26.74/3.72  fof(f106,plain,(
% 26.74/3.72    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X1,X0),k1_tarski(X0))) )),
% 26.74/3.72    inference(backward_demodulation,[],[f42,f105])).
% 26.74/3.72  fof(f105,plain,(
% 26.74/3.72    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 26.74/3.72    inference(forward_demodulation,[],[f103,f22])).
% 26.74/3.72  fof(f103,plain,(
% 26.74/3.72    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 26.74/3.72    inference(superposition,[],[f52,f26])).
% 26.74/3.72  fof(f52,plain,(
% 26.74/3.72    ( ! [X2,X0,X1] : (k1_enumset1(X1,X0,X2) = k2_enumset1(X0,X1,X2,X1)) )),
% 26.74/3.72    inference(superposition,[],[f31,f28])).
% 26.74/3.72  fof(f28,plain,(
% 26.74/3.72    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)) )),
% 26.74/3.72    inference(cnf_transformation,[],[f2])).
% 26.74/3.72  fof(f2,axiom,(
% 26.74/3.72    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 26.74/3.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 26.74/3.72  fof(f42,plain,(
% 26.74/3.72    ( ! [X0,X1] : (k1_enumset1(X0,X1,X0) = k2_xboole_0(k2_tarski(X1,X0),k1_tarski(X0))) )),
% 26.74/3.72    inference(superposition,[],[f28,f21])).
% 26.74/3.72  fof(f120,plain,(
% 26.74/3.72    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 26.74/3.72    inference(backward_demodulation,[],[f108,f119])).
% 26.74/3.72  fof(f119,plain,(
% 26.74/3.72    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 26.74/3.72    inference(forward_demodulation,[],[f117,f32])).
% 26.74/3.72  fof(f117,plain,(
% 26.74/3.72    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 26.74/3.72    inference(superposition,[],[f35,f26])).
% 26.74/3.72  fof(f108,plain,(
% 26.74/3.72    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 26.74/3.72    inference(superposition,[],[f34,f21])).
% 26.74/3.72  fof(f35,plain,(
% 26.74/3.72    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 26.74/3.72    inference(cnf_transformation,[],[f6])).
% 26.74/3.72  fof(f6,axiom,(
% 26.74/3.72    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 26.74/3.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 26.74/3.72  fof(f20,plain,(
% 26.74/3.72    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 26.74/3.72    inference(cnf_transformation,[],[f19])).
% 26.74/3.72  fof(f19,plain,(
% 26.74/3.72    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 26.74/3.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).
% 26.74/3.72  fof(f18,plain,(
% 26.74/3.72    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 26.74/3.72    introduced(choice_axiom,[])).
% 26.74/3.72  fof(f17,plain,(
% 26.74/3.72    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 26.74/3.72    inference(ennf_transformation,[],[f16])).
% 26.74/3.72  fof(f16,negated_conjecture,(
% 26.74/3.72    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 26.74/3.72    inference(negated_conjecture,[],[f15])).
% 26.74/3.72  fof(f15,conjecture,(
% 26.74/3.72    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 26.74/3.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).
% 26.74/3.72  % SZS output end Proof for theBenchmark
% 26.74/3.72  % (7434)------------------------------
% 26.74/3.72  % (7434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 26.74/3.72  % (7434)Termination reason: Refutation
% 26.74/3.72  
% 26.74/3.72  % (7434)Memory used [KB]: 48613
% 26.74/3.72  % (7434)Time elapsed: 3.277 s
% 26.74/3.72  % (7434)------------------------------
% 26.74/3.72  % (7434)------------------------------
% 26.86/3.74  % (7430)Success in time 3.37 s
%------------------------------------------------------------------------------

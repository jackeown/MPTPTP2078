%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:58 EST 2020

% Result     : Theorem 27.95s
% Output     : Refutation 27.95s
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
fof(f35601,plain,(
    $false ),
    inference(subsumption_resolution,[],[f35600,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f35600,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4)) ),
    inference(forward_demodulation,[],[f35444,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f35444,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f4389,f1715])).

fof(f1715,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5)) ),
    inference(forward_demodulation,[],[f1696,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f4389,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4)) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f111,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X2,X3,X0,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f34,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(f674,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X6,X6,X7) = k2_enumset1(X4,X6,X5,X7) ),
    inference(forward_demodulation,[],[f662,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(superposition,[],[f31,f21])).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(f20,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.41  % (23404)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.44  % (23413)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.45  % (23400)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.46  % (23398)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.47  % (23411)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.47  % (23407)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.47  % (23407)Refutation not found, incomplete strategy% (23407)------------------------------
% 0.19/0.47  % (23407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (23407)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (23407)Memory used [KB]: 10618
% 0.19/0.47  % (23407)Time elapsed: 0.062 s
% 0.19/0.47  % (23407)------------------------------
% 0.19/0.47  % (23407)------------------------------
% 0.19/0.49  % (23401)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.49  % (23396)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.49  % (23399)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.50  % (23408)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.50  % (23410)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.50  % (23397)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.50  % (23402)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.51  % (23405)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.51  % (23412)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.51  % (23409)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.51  % (23403)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.52  % (23406)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 4.66/1.01  % (23400)Time limit reached!
% 4.66/1.01  % (23400)------------------------------
% 4.66/1.01  % (23400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.66/1.01  % (23400)Termination reason: Time limit
% 4.66/1.01  % (23400)Termination phase: Saturation
% 4.66/1.01  
% 4.66/1.01  % (23400)Memory used [KB]: 11129
% 4.66/1.01  % (23400)Time elapsed: 0.600 s
% 4.66/1.01  % (23400)------------------------------
% 4.66/1.01  % (23400)------------------------------
% 12.39/1.91  % (23401)Time limit reached!
% 12.39/1.91  % (23401)------------------------------
% 12.39/1.91  % (23401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.39/1.91  % (23401)Termination reason: Time limit
% 12.39/1.91  % (23401)Termination phase: Saturation
% 12.39/1.91  
% 12.39/1.91  % (23401)Memory used [KB]: 33133
% 12.39/1.91  % (23401)Time elapsed: 1.500 s
% 12.39/1.91  % (23401)------------------------------
% 12.39/1.91  % (23401)------------------------------
% 12.39/1.95  % (23402)Time limit reached!
% 12.39/1.95  % (23402)------------------------------
% 12.39/1.95  % (23402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.39/1.95  % (23402)Termination reason: Time limit
% 12.39/1.95  % (23402)Termination phase: Saturation
% 12.39/1.95  
% 12.39/1.95  % (23402)Memory used [KB]: 22387
% 12.39/1.95  % (23402)Time elapsed: 1.500 s
% 12.39/1.95  % (23402)------------------------------
% 12.39/1.95  % (23402)------------------------------
% 14.86/2.23  % (23398)Time limit reached!
% 14.86/2.23  % (23398)------------------------------
% 14.86/2.23  % (23398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.86/2.23  % (23398)Termination reason: Time limit
% 14.86/2.23  
% 14.86/2.23  % (23398)Memory used [KB]: 23027
% 14.86/2.23  % (23398)Time elapsed: 1.822 s
% 14.86/2.23  % (23398)------------------------------
% 14.86/2.23  % (23398)------------------------------
% 17.84/2.61  % (23408)Time limit reached!
% 17.84/2.61  % (23408)------------------------------
% 17.84/2.61  % (23408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.84/2.61  % (23408)Termination reason: Time limit
% 17.84/2.61  % (23408)Termination phase: Saturation
% 17.84/2.61  
% 17.84/2.61  % (23408)Memory used [KB]: 12409
% 17.84/2.61  % (23408)Time elapsed: 2.200 s
% 17.84/2.61  % (23408)------------------------------
% 17.84/2.61  % (23408)------------------------------
% 27.95/3.86  % (23399)Refutation found. Thanks to Tanya!
% 27.95/3.86  % SZS status Theorem for theBenchmark
% 27.95/3.86  % SZS output start Proof for theBenchmark
% 27.95/3.86  fof(f35601,plain,(
% 27.95/3.86    $false),
% 27.95/3.86    inference(subsumption_resolution,[],[f35600,f24])).
% 27.95/3.86  fof(f24,plain,(
% 27.95/3.86    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 27.95/3.86    inference(cnf_transformation,[],[f14])).
% 27.95/3.86  fof(f14,axiom,(
% 27.95/3.86    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 27.95/3.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 27.95/3.86  fof(f35600,plain,(
% 27.95/3.86    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4))),
% 27.95/3.86    inference(forward_demodulation,[],[f35444,f30])).
% 27.95/3.86  fof(f30,plain,(
% 27.95/3.86    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 27.95/3.86    inference(cnf_transformation,[],[f12])).
% 27.95/3.86  fof(f12,axiom,(
% 27.95/3.86    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 27.95/3.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 27.95/3.86  fof(f35444,plain,(
% 27.95/3.86    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK4))),
% 27.95/3.86    inference(superposition,[],[f4389,f1715])).
% 27.95/3.86  fof(f1715,plain,(
% 27.95/3.86    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5))) )),
% 27.95/3.86    inference(forward_demodulation,[],[f1696,f25])).
% 27.95/3.86  fof(f25,plain,(
% 27.95/3.86    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 27.95/3.86    inference(cnf_transformation,[],[f13])).
% 27.95/3.86  fof(f13,axiom,(
% 27.95/3.86    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 27.95/3.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 27.95/3.86  fof(f1696,plain,(
% 27.95/3.86    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5))) )),
% 27.95/3.86    inference(superposition,[],[f145,f25])).
% 27.95/3.86  fof(f145,plain,(
% 27.95/3.86    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 27.95/3.86    inference(forward_demodulation,[],[f134,f25])).
% 27.95/3.86  fof(f134,plain,(
% 27.95/3.86    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 27.95/3.86    inference(superposition,[],[f33,f25])).
% 27.95/3.86  fof(f33,plain,(
% 27.95/3.86    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 27.95/3.86    inference(cnf_transformation,[],[f11])).
% 27.95/3.86  fof(f11,axiom,(
% 27.95/3.86    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 27.95/3.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 27.95/3.86  fof(f4389,plain,(
% 27.95/3.86    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4))),
% 27.95/3.86    inference(superposition,[],[f20,f4288])).
% 27.95/3.86  fof(f4288,plain,(
% 27.95/3.86    ( ! [X14,X12,X13,X11] : (k2_enumset1(X11,X12,X13,X14) = k2_enumset1(X11,X13,X12,X14)) )),
% 27.95/3.86    inference(superposition,[],[f674,f112])).
% 27.95/3.86  fof(f112,plain,(
% 27.95/3.86    ( ! [X2,X0,X3,X1] : (k3_enumset1(X2,X3,X0,X0,X1) = k2_enumset1(X2,X3,X0,X1)) )),
% 27.95/3.86    inference(forward_demodulation,[],[f111,f31])).
% 27.95/3.86  fof(f31,plain,(
% 27.95/3.86    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 27.95/3.86    inference(cnf_transformation,[],[f1])).
% 27.95/3.86  fof(f1,axiom,(
% 27.95/3.86    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 27.95/3.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 27.95/3.86  fof(f111,plain,(
% 27.95/3.86    ( ! [X2,X0,X3,X1] : (k3_enumset1(X2,X3,X0,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) )),
% 27.95/3.86    inference(superposition,[],[f34,f22])).
% 27.95/3.86  fof(f22,plain,(
% 27.95/3.86    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 27.95/3.86    inference(cnf_transformation,[],[f8])).
% 27.95/3.86  fof(f8,axiom,(
% 27.95/3.86    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 27.95/3.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 27.95/3.86  fof(f34,plain,(
% 27.95/3.86    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 27.95/3.86    inference(cnf_transformation,[],[f5])).
% 27.95/3.86  fof(f5,axiom,(
% 27.95/3.86    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 27.95/3.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).
% 27.95/3.86  fof(f674,plain,(
% 27.95/3.86    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X6,X6,X7) = k2_enumset1(X4,X6,X5,X7)) )),
% 27.95/3.86    inference(forward_demodulation,[],[f662,f32])).
% 27.95/3.86  fof(f32,plain,(
% 27.95/3.86    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 27.95/3.86    inference(cnf_transformation,[],[f4])).
% 27.95/3.86  fof(f4,axiom,(
% 27.95/3.86    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 27.95/3.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 27.95/3.86  fof(f662,plain,(
% 27.95/3.86    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X6,X6,X7) = k2_xboole_0(k1_enumset1(X4,X6,X5),k1_tarski(X7))) )),
% 27.95/3.86    inference(superposition,[],[f35,f303])).
% 27.95/3.86  fof(f303,plain,(
% 27.95/3.86    ( ! [X10,X11,X9] : (k2_enumset1(X11,X9,X10,X10) = k1_enumset1(X11,X10,X9)) )),
% 27.95/3.86    inference(forward_demodulation,[],[f294,f56])).
% 27.95/3.86  fof(f56,plain,(
% 27.95/3.86    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 27.95/3.86    inference(forward_demodulation,[],[f50,f26])).
% 27.95/3.86  fof(f26,plain,(
% 27.95/3.86    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.95/3.86    inference(cnf_transformation,[],[f9])).
% 27.95/3.86  fof(f9,axiom,(
% 27.95/3.86    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.95/3.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 27.95/3.86  fof(f50,plain,(
% 27.95/3.86    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 27.95/3.86    inference(superposition,[],[f31,f21])).
% 27.95/3.86  fof(f21,plain,(
% 27.95/3.86    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 27.95/3.86    inference(cnf_transformation,[],[f7])).
% 27.95/3.86  fof(f7,axiom,(
% 27.95/3.86    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 27.95/3.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 27.95/3.86  fof(f294,plain,(
% 27.95/3.86    ( ! [X10,X11,X9] : (k2_enumset1(X11,X9,X10,X10) = k2_xboole_0(k1_tarski(X11),k2_tarski(X10,X9))) )),
% 27.95/3.86    inference(superposition,[],[f120,f173])).
% 27.95/3.86  fof(f173,plain,(
% 27.95/3.86    ( ! [X0,X1] : (k2_tarski(X1,X0) = k1_enumset1(X0,X1,X1)) )),
% 27.95/3.86    inference(superposition,[],[f106,f27])).
% 27.95/3.86  fof(f27,plain,(
% 27.95/3.86    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 27.95/3.86    inference(cnf_transformation,[],[f3])).
% 27.95/3.86  fof(f3,axiom,(
% 27.95/3.86    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 27.95/3.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 27.95/3.86  fof(f106,plain,(
% 27.95/3.86    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X1,X0),k1_tarski(X0))) )),
% 27.95/3.86    inference(backward_demodulation,[],[f42,f105])).
% 27.95/3.86  fof(f105,plain,(
% 27.95/3.86    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 27.95/3.86    inference(forward_demodulation,[],[f103,f22])).
% 27.95/3.86  fof(f103,plain,(
% 27.95/3.86    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 27.95/3.86    inference(superposition,[],[f52,f26])).
% 27.95/3.86  fof(f52,plain,(
% 27.95/3.86    ( ! [X2,X0,X1] : (k1_enumset1(X1,X0,X2) = k2_enumset1(X0,X1,X2,X1)) )),
% 27.95/3.86    inference(superposition,[],[f31,f28])).
% 27.95/3.86  fof(f28,plain,(
% 27.95/3.86    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)) )),
% 27.95/3.86    inference(cnf_transformation,[],[f2])).
% 27.95/3.86  fof(f2,axiom,(
% 27.95/3.86    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 27.95/3.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 27.95/3.86  fof(f42,plain,(
% 27.95/3.86    ( ! [X0,X1] : (k1_enumset1(X0,X1,X0) = k2_xboole_0(k2_tarski(X1,X0),k1_tarski(X0))) )),
% 27.95/3.86    inference(superposition,[],[f28,f21])).
% 27.95/3.86  fof(f120,plain,(
% 27.95/3.86    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 27.95/3.86    inference(backward_demodulation,[],[f108,f119])).
% 27.95/3.86  fof(f119,plain,(
% 27.95/3.86    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 27.95/3.86    inference(forward_demodulation,[],[f117,f32])).
% 27.95/3.86  fof(f117,plain,(
% 27.95/3.86    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 27.95/3.86    inference(superposition,[],[f35,f26])).
% 27.95/3.86  fof(f108,plain,(
% 27.95/3.86    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 27.95/3.86    inference(superposition,[],[f34,f21])).
% 27.95/3.86  fof(f35,plain,(
% 27.95/3.86    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 27.95/3.86    inference(cnf_transformation,[],[f6])).
% 27.95/3.86  fof(f6,axiom,(
% 27.95/3.86    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 27.95/3.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 27.95/3.86  fof(f20,plain,(
% 27.95/3.86    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 27.95/3.86    inference(cnf_transformation,[],[f19])).
% 27.95/3.86  fof(f19,plain,(
% 27.95/3.86    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 27.95/3.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).
% 27.95/3.86  fof(f18,plain,(
% 27.95/3.86    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 27.95/3.86    introduced(choice_axiom,[])).
% 27.95/3.86  fof(f17,plain,(
% 27.95/3.86    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 27.95/3.86    inference(ennf_transformation,[],[f16])).
% 27.95/3.86  fof(f16,negated_conjecture,(
% 27.95/3.86    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 27.95/3.86    inference(negated_conjecture,[],[f15])).
% 27.95/3.86  fof(f15,conjecture,(
% 27.95/3.86    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 27.95/3.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
% 27.95/3.86  % SZS output end Proof for theBenchmark
% 27.95/3.86  % (23399)------------------------------
% 27.95/3.86  % (23399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 27.95/3.86  % (23399)Termination reason: Refutation
% 27.95/3.86  
% 27.95/3.86  % (23399)Memory used [KB]: 48357
% 27.95/3.86  % (23399)Time elapsed: 3.433 s
% 27.95/3.86  % (23399)------------------------------
% 27.95/3.86  % (23399)------------------------------
% 28.11/3.88  % (23395)Success in time 3.528 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:59:02 EST 2020

% Result     : Theorem 27.71s
% Output     : Refutation 27.71s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 123 expanded)
%              Number of leaves         :   15 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :   61 ( 125 expanded)
%              Number of equality atoms :   60 ( 124 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58800,plain,(
    $false ),
    inference(subsumption_resolution,[],[f58799,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f58799,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(forward_demodulation,[],[f58617,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f58617,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f13144,f2382])).

fof(f2382,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5)) ),
    inference(forward_demodulation,[],[f2356,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f2356,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5)) ),
    inference(superposition,[],[f235,f29])).

fof(f235,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f224,f29])).

fof(f224,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(superposition,[],[f37,f29])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f13144,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(superposition,[],[f11744,f8087])).

fof(f8087,plain,(
    ! [X123,X121,X124,X122] : k2_enumset1(X122,X123,X124,X121) = k2_enumset1(X122,X123,X121,X124) ),
    inference(superposition,[],[f7896,f492])).

fof(f492,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6) ),
    inference(superposition,[],[f73,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f73,plain,(
    ! [X6,X4,X7,X5] : k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7) ),
    inference(superposition,[],[f34,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f7896,plain,(
    ! [X12,X10,X13,X11] : k2_enumset1(X10,X11,X12,X13) = k2_enumset1(X12,X10,X11,X13) ),
    inference(superposition,[],[f301,f211])).

fof(f211,plain,(
    ! [X10,X8,X11,X9] : k2_enumset1(X8,X9,X10,X11) = k3_enumset1(X8,X9,X9,X10,X11) ),
    inference(forward_demodulation,[],[f204,f36])).

fof(f204,plain,(
    ! [X10,X8,X11,X9] : k2_xboole_0(k1_enumset1(X8,X9,X10),k1_tarski(X11)) = k3_enumset1(X8,X9,X9,X10,X11) ),
    inference(superposition,[],[f39,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X2,X0,X1) = k2_enumset1(X2,X0,X0,X1) ),
    inference(forward_demodulation,[],[f71,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f71,plain,(
    ! [X2,X0,X1] : k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f34,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f301,plain,(
    ! [X10,X8,X7,X9] : k3_enumset1(X7,X8,X8,X9,X10) = k2_enumset1(X9,X7,X8,X10) ),
    inference(forward_demodulation,[],[f294,f36])).

fof(f294,plain,(
    ! [X10,X8,X7,X9] : k3_enumset1(X7,X8,X8,X9,X10) = k2_xboole_0(k1_enumset1(X9,X7,X8),k1_tarski(X10)) ),
    inference(superposition,[],[f39,f105])).

fof(f105,plain,(
    ! [X4,X5,X3] : k1_enumset1(X5,X3,X4) = k2_enumset1(X3,X4,X4,X5) ),
    inference(forward_demodulation,[],[f99,f66])).

fof(f66,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5) ),
    inference(superposition,[],[f31,f24])).

fof(f99,plain,(
    ! [X4,X5,X3] : k2_enumset1(X3,X4,X4,X5) = k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5)) ),
    inference(superposition,[],[f36,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X1,X0) = k1_enumset1(X1,X0,X0) ),
    inference(forward_demodulation,[],[f63,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f31,f23])).

fof(f23,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f11744,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK2,sK3)) ),
    inference(superposition,[],[f22,f8028])).

fof(f8028,plain,(
    ! [X116,X114,X115,X113] : k2_enumset1(X115,X116,X113,X114) = k2_enumset1(X115,X113,X114,X116) ),
    inference(superposition,[],[f7896,f528])).

fof(f528,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X6,X7,X4,X5) ),
    inference(superposition,[],[f90,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f90,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f35,f24])).

fof(f22,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))
   => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (30881)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.45  % (30872)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (30873)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (30869)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (30882)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (30876)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (30871)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (30874)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (30879)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (30880)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (30878)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (30883)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (30877)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (30886)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (30875)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (30870)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (30885)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (30884)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (30880)Refutation not found, incomplete strategy% (30880)------------------------------
% 0.21/0.51  % (30880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30880)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30880)Memory used [KB]: 10618
% 0.21/0.51  % (30880)Time elapsed: 0.103 s
% 0.21/0.51  % (30880)------------------------------
% 0.21/0.51  % (30880)------------------------------
% 4.94/1.02  % (30873)Time limit reached!
% 4.94/1.02  % (30873)------------------------------
% 4.94/1.02  % (30873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.94/1.02  % (30873)Termination reason: Time limit
% 4.94/1.02  % (30873)Termination phase: Saturation
% 4.94/1.02  
% 4.94/1.02  % (30873)Memory used [KB]: 11385
% 4.94/1.02  % (30873)Time elapsed: 0.612 s
% 4.94/1.02  % (30873)------------------------------
% 4.94/1.02  % (30873)------------------------------
% 11.96/1.92  % (30874)Time limit reached!
% 11.96/1.92  % (30874)------------------------------
% 11.96/1.92  % (30874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.96/1.92  % (30874)Termination reason: Time limit
% 11.96/1.92  % (30874)Termination phase: Saturation
% 11.96/1.92  
% 11.96/1.92  % (30874)Memory used [KB]: 31470
% 11.96/1.92  % (30874)Time elapsed: 1.500 s
% 11.96/1.92  % (30874)------------------------------
% 11.96/1.92  % (30874)------------------------------
% 12.64/1.96  % (30875)Time limit reached!
% 12.64/1.96  % (30875)------------------------------
% 12.64/1.96  % (30875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.64/1.96  % (30875)Termination reason: Time limit
% 12.64/1.96  
% 12.64/1.96  % (30875)Memory used [KB]: 26481
% 12.64/1.96  % (30875)Time elapsed: 1.501 s
% 12.64/1.96  % (30875)------------------------------
% 12.64/1.96  % (30875)------------------------------
% 14.48/2.22  % (30871)Time limit reached!
% 14.48/2.22  % (30871)------------------------------
% 14.48/2.22  % (30871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.48/2.22  % (30871)Termination reason: Time limit
% 14.48/2.22  
% 14.48/2.22  % (30871)Memory used [KB]: 16886
% 14.48/2.22  % (30871)Time elapsed: 1.812 s
% 14.48/2.22  % (30871)------------------------------
% 14.48/2.22  % (30871)------------------------------
% 17.87/2.61  % (30881)Time limit reached!
% 17.87/2.61  % (30881)------------------------------
% 17.87/2.61  % (30881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.87/2.61  % (30881)Termination reason: Time limit
% 17.87/2.61  % (30881)Termination phase: Saturation
% 17.87/2.61  
% 17.87/2.61  % (30881)Memory used [KB]: 23539
% 17.87/2.61  % (30881)Time elapsed: 2.200 s
% 17.87/2.61  % (30881)------------------------------
% 17.87/2.61  % (30881)------------------------------
% 27.71/3.84  % (30872)Refutation found. Thanks to Tanya!
% 27.71/3.84  % SZS status Theorem for theBenchmark
% 27.71/3.84  % SZS output start Proof for theBenchmark
% 27.71/3.84  fof(f58800,plain,(
% 27.71/3.84    $false),
% 27.71/3.84    inference(subsumption_resolution,[],[f58799,f28])).
% 27.71/3.84  fof(f28,plain,(
% 27.71/3.84    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 27.71/3.84    inference(cnf_transformation,[],[f16])).
% 27.71/3.84  fof(f16,axiom,(
% 27.71/3.84    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 27.71/3.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 27.71/3.84  fof(f58799,plain,(
% 27.71/3.84    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4))),
% 27.71/3.84    inference(forward_demodulation,[],[f58617,f32])).
% 27.71/3.84  fof(f32,plain,(
% 27.71/3.84    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 27.71/3.84    inference(cnf_transformation,[],[f14])).
% 27.71/3.84  fof(f14,axiom,(
% 27.71/3.84    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 27.71/3.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 27.71/3.84  fof(f58617,plain,(
% 27.71/3.84    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4))),
% 27.71/3.84    inference(superposition,[],[f13144,f2382])).
% 27.71/3.84  fof(f2382,plain,(
% 27.71/3.84    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5))) )),
% 27.71/3.84    inference(forward_demodulation,[],[f2356,f29])).
% 27.71/3.84  fof(f29,plain,(
% 27.71/3.84    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 27.71/3.84    inference(cnf_transformation,[],[f15])).
% 27.71/3.84  fof(f15,axiom,(
% 27.71/3.84    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 27.71/3.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 27.71/3.84  fof(f2356,plain,(
% 27.71/3.84    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5))) )),
% 27.71/3.84    inference(superposition,[],[f235,f29])).
% 27.71/3.84  fof(f235,plain,(
% 27.71/3.84    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 27.71/3.84    inference(forward_demodulation,[],[f224,f29])).
% 27.71/3.84  fof(f224,plain,(
% 27.71/3.84    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 27.71/3.84    inference(superposition,[],[f37,f29])).
% 27.71/3.84  fof(f37,plain,(
% 27.71/3.84    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 27.71/3.84    inference(cnf_transformation,[],[f13])).
% 27.71/3.84  fof(f13,axiom,(
% 27.71/3.84    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 27.71/3.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 27.71/3.84  fof(f13144,plain,(
% 27.71/3.84    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4))),
% 27.71/3.84    inference(superposition,[],[f11744,f8087])).
% 27.71/3.84  fof(f8087,plain,(
% 27.71/3.84    ( ! [X123,X121,X124,X122] : (k2_enumset1(X122,X123,X124,X121) = k2_enumset1(X122,X123,X121,X124)) )),
% 27.71/3.84    inference(superposition,[],[f7896,f492])).
% 27.71/3.84  fof(f492,plain,(
% 27.71/3.84    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6)) )),
% 27.71/3.84    inference(superposition,[],[f73,f36])).
% 27.71/3.84  fof(f36,plain,(
% 27.71/3.84    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 27.71/3.84    inference(cnf_transformation,[],[f6])).
% 27.71/3.84  fof(f6,axiom,(
% 27.71/3.84    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 27.71/3.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 27.71/3.84  fof(f73,plain,(
% 27.71/3.84    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)) )),
% 27.71/3.84    inference(superposition,[],[f34,f24])).
% 27.71/3.84  fof(f24,plain,(
% 27.71/3.84    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 27.71/3.84    inference(cnf_transformation,[],[f1])).
% 27.71/3.84  fof(f1,axiom,(
% 27.71/3.84    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 27.71/3.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 27.71/3.84  fof(f34,plain,(
% 27.71/3.84    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 27.71/3.84    inference(cnf_transformation,[],[f5])).
% 27.71/3.84  fof(f5,axiom,(
% 27.71/3.84    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 27.71/3.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 27.71/3.84  fof(f7896,plain,(
% 27.71/3.84    ( ! [X12,X10,X13,X11] : (k2_enumset1(X10,X11,X12,X13) = k2_enumset1(X12,X10,X11,X13)) )),
% 27.71/3.84    inference(superposition,[],[f301,f211])).
% 27.71/3.84  fof(f211,plain,(
% 27.71/3.84    ( ! [X10,X8,X11,X9] : (k2_enumset1(X8,X9,X10,X11) = k3_enumset1(X8,X9,X9,X10,X11)) )),
% 27.71/3.84    inference(forward_demodulation,[],[f204,f36])).
% 27.71/3.84  fof(f204,plain,(
% 27.71/3.84    ( ! [X10,X8,X11,X9] : (k2_xboole_0(k1_enumset1(X8,X9,X10),k1_tarski(X11)) = k3_enumset1(X8,X9,X9,X10,X11)) )),
% 27.71/3.84    inference(superposition,[],[f39,f77])).
% 27.71/3.84  fof(f77,plain,(
% 27.71/3.84    ( ! [X2,X0,X1] : (k1_enumset1(X2,X0,X1) = k2_enumset1(X2,X0,X0,X1)) )),
% 27.71/3.84    inference(forward_demodulation,[],[f71,f31])).
% 27.71/3.84  fof(f31,plain,(
% 27.71/3.84    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 27.71/3.84    inference(cnf_transformation,[],[f4])).
% 27.71/3.84  fof(f4,axiom,(
% 27.71/3.84    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 27.71/3.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 27.71/3.84  fof(f71,plain,(
% 27.71/3.84    ( ! [X2,X0,X1] : (k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))) )),
% 27.71/3.84    inference(superposition,[],[f34,f26])).
% 27.71/3.84  fof(f26,plain,(
% 27.71/3.84    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 27.71/3.84    inference(cnf_transformation,[],[f10])).
% 27.71/3.84  fof(f10,axiom,(
% 27.71/3.84    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 27.71/3.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 27.71/3.84  fof(f39,plain,(
% 27.71/3.84    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 27.71/3.84    inference(cnf_transformation,[],[f8])).
% 27.71/3.84  fof(f8,axiom,(
% 27.71/3.84    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 27.71/3.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 27.71/3.84  fof(f301,plain,(
% 27.71/3.84    ( ! [X10,X8,X7,X9] : (k3_enumset1(X7,X8,X8,X9,X10) = k2_enumset1(X9,X7,X8,X10)) )),
% 27.71/3.84    inference(forward_demodulation,[],[f294,f36])).
% 27.71/3.84  fof(f294,plain,(
% 27.71/3.84    ( ! [X10,X8,X7,X9] : (k3_enumset1(X7,X8,X8,X9,X10) = k2_xboole_0(k1_enumset1(X9,X7,X8),k1_tarski(X10))) )),
% 27.71/3.84    inference(superposition,[],[f39,f105])).
% 27.71/3.84  fof(f105,plain,(
% 27.71/3.84    ( ! [X4,X5,X3] : (k1_enumset1(X5,X3,X4) = k2_enumset1(X3,X4,X4,X5)) )),
% 27.71/3.84    inference(forward_demodulation,[],[f99,f66])).
% 27.71/3.84  fof(f66,plain,(
% 27.71/3.84    ( ! [X4,X5,X3] : (k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5)) )),
% 27.71/3.84    inference(superposition,[],[f31,f24])).
% 27.71/3.84  fof(f99,plain,(
% 27.71/3.84    ( ! [X4,X5,X3] : (k2_enumset1(X3,X4,X4,X5) = k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5))) )),
% 27.71/3.84    inference(superposition,[],[f36,f70])).
% 27.71/3.84  fof(f70,plain,(
% 27.71/3.84    ( ! [X0,X1] : (k2_tarski(X1,X0) = k1_enumset1(X1,X0,X0)) )),
% 27.71/3.84    inference(forward_demodulation,[],[f63,f27])).
% 27.71/3.84  fof(f27,plain,(
% 27.71/3.84    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 27.71/3.84    inference(cnf_transformation,[],[f3])).
% 27.71/3.84  fof(f3,axiom,(
% 27.71/3.84    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 27.71/3.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 27.71/3.84  fof(f63,plain,(
% 27.71/3.84    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) = k1_enumset1(X1,X0,X0)) )),
% 27.71/3.84    inference(superposition,[],[f31,f23])).
% 27.71/3.84  fof(f23,plain,(
% 27.71/3.84    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 27.71/3.84    inference(cnf_transformation,[],[f9])).
% 27.71/3.84  fof(f9,axiom,(
% 27.71/3.84    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 27.71/3.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 27.71/3.84  fof(f11744,plain,(
% 27.71/3.84    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK2,sK3))),
% 27.71/3.84    inference(superposition,[],[f22,f8028])).
% 27.71/3.84  fof(f8028,plain,(
% 27.71/3.84    ( ! [X116,X114,X115,X113] : (k2_enumset1(X115,X116,X113,X114) = k2_enumset1(X115,X113,X114,X116)) )),
% 27.71/3.84    inference(superposition,[],[f7896,f528])).
% 27.71/3.84  fof(f528,plain,(
% 27.71/3.84    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X6,X7,X4,X5)) )),
% 27.71/3.84    inference(superposition,[],[f90,f35])).
% 27.71/3.84  fof(f35,plain,(
% 27.71/3.84    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 27.71/3.84    inference(cnf_transformation,[],[f2])).
% 27.71/3.84  fof(f2,axiom,(
% 27.71/3.84    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 27.71/3.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 27.71/3.84  fof(f90,plain,(
% 27.71/3.84    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5))) )),
% 27.71/3.84    inference(superposition,[],[f35,f24])).
% 27.71/3.84  fof(f22,plain,(
% 27.71/3.84    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 27.71/3.84    inference(cnf_transformation,[],[f21])).
% 27.71/3.84  fof(f21,plain,(
% 27.71/3.84    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 27.71/3.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f20])).
% 27.71/3.84  fof(f20,plain,(
% 27.71/3.84    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 27.71/3.84    introduced(choice_axiom,[])).
% 27.71/3.84  fof(f19,plain,(
% 27.71/3.84    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 27.71/3.84    inference(ennf_transformation,[],[f18])).
% 27.71/3.84  fof(f18,negated_conjecture,(
% 27.71/3.84    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 27.71/3.84    inference(negated_conjecture,[],[f17])).
% 27.71/3.84  fof(f17,conjecture,(
% 27.71/3.84    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 27.71/3.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).
% 27.71/3.84  % SZS output end Proof for theBenchmark
% 27.71/3.84  % (30872)------------------------------
% 27.71/3.84  % (30872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 27.71/3.84  % (30872)Termination reason: Refutation
% 27.71/3.84  
% 27.71/3.84  % (30872)Memory used [KB]: 74838
% 27.71/3.84  % (30872)Time elapsed: 3.416 s
% 27.71/3.84  % (30872)------------------------------
% 27.71/3.84  % (30872)------------------------------
% 27.71/3.85  % (30868)Success in time 3.49 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 261 expanded)
%              Number of leaves         :   12 (  87 expanded)
%              Depth                    :   19
%              Number of atoms          :   60 ( 262 expanded)
%              Number of equality atoms :   59 ( 261 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f288,plain,(
    $false ),
    inference(subsumption_resolution,[],[f285,f257])).

fof(f257,plain,(
    ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k2_enumset1(X3,X4,X3,X5) ),
    inference(forward_demodulation,[],[f253,f158])).

fof(f158,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2) ),
    inference(forward_demodulation,[],[f155,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f155,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2) ),
    inference(superposition,[],[f147,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f147,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3) ),
    inference(forward_demodulation,[],[f143,f29])).

fof(f143,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3) ),
    inference(superposition,[],[f138,f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f138,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4) ),
    inference(forward_demodulation,[],[f135,f30])).

fof(f135,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4) ),
    inference(superposition,[],[f129,f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f129,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X3,X4,X5,X5) ),
    inference(forward_demodulation,[],[f127,f31])).

fof(f127,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X3,X4,X5,X5) ),
    inference(superposition,[],[f126,f32])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f126,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0) = k5_enumset1(X1,X2,X3,X4,X5,X6,X0) ),
    inference(backward_demodulation,[],[f122,f125])).

fof(f125,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(forward_demodulation,[],[f124,f32])).

fof(f124,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(superposition,[],[f34,f31])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f122,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0)) ),
    inference(superposition,[],[f33,f21])).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

fof(f253,plain,(
    ! [X4,X5,X3] : k2_enumset1(X3,X4,X3,X5) = k2_enumset1(X3,X4,X5,X5) ),
    inference(superposition,[],[f184,f147])).

fof(f184,plain,(
    ! [X47,X45,X46,X44] : k3_enumset1(X44,X45,X44,X46,X47) = k2_enumset1(X44,X45,X46,X47) ),
    inference(forward_demodulation,[],[f180,f183])).

fof(f183,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f171,f29])).

fof(f171,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f153,f22])).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f153,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f151,f30])).

fof(f151,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f133,f28])).

fof(f133,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(forward_demodulation,[],[f131,f31])).

fof(f131,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f123,f29])).

fof(f123,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(forward_demodulation,[],[f121,f32])).

fof(f121,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(superposition,[],[f33,f30])).

fof(f180,plain,(
    ! [X47,X45,X46,X44] : k3_enumset1(X44,X45,X44,X46,X47) = k2_xboole_0(k2_tarski(X44,X45),k2_tarski(X46,X47)) ),
    inference(superposition,[],[f153,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f25,f22])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(f285,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2) ),
    inference(superposition,[],[f203,f183])).

fof(f203,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2)) ),
    inference(forward_demodulation,[],[f202,f187])).

fof(f187,plain,(
    ! [X2,X3] : k2_tarski(X2,X3) = k2_tarski(X3,X2) ),
    inference(superposition,[],[f168,f22])).

fof(f168,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X1,X0) ),
    inference(forward_demodulation,[],[f165,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f25,f22])).

fof(f165,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X0,X1,X1) ),
    inference(superposition,[],[f158,f28])).

fof(f202,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2)) ),
    inference(backward_demodulation,[],[f20,f187])).

fof(f20,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:57:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (29390)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (29395)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (29398)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (29389)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (29403)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (29400)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (29399)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (29397)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (29402)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (29391)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (29394)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (29392)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (29390)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (29398)Refutation not found, incomplete strategy% (29398)------------------------------
% 0.21/0.49  % (29398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29398)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (29398)Memory used [KB]: 10618
% 0.21/0.49  % (29398)Time elapsed: 0.065 s
% 0.21/0.49  % (29398)------------------------------
% 0.21/0.49  % (29398)------------------------------
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f285,f257])).
% 0.21/0.49  fof(f257,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k2_enumset1(X3,X4,X3,X5)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f253,f158])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f155,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)) )),
% 0.21/0.49    inference(superposition,[],[f147,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f143,f29])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)) )),
% 0.21/0.49    inference(superposition,[],[f138,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f135,f30])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) )),
% 0.21/0.49    inference(superposition,[],[f129,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X3,X4,X5,X5)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f127,f31])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X3,X4,X5,X5)) )),
% 0.21/0.49    inference(superposition,[],[f126,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0) = k5_enumset1(X1,X2,X3,X4,X5,X6,X0)) )),
% 0.21/0.49    inference(backward_demodulation,[],[f122,f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f124,f32])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 0.21/0.49    inference(superposition,[],[f34,f31])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0))) )),
% 0.21/0.49    inference(superposition,[],[f33,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (k2_enumset1(X3,X4,X3,X5) = k2_enumset1(X3,X4,X5,X5)) )),
% 0.21/0.49    inference(superposition,[],[f184,f147])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    ( ! [X47,X45,X46,X44] : (k3_enumset1(X44,X45,X44,X46,X47) = k2_enumset1(X44,X45,X46,X47)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f180,f183])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f171,f29])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.49    inference(superposition,[],[f153,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f151,f30])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.21/0.49    inference(superposition,[],[f133,f28])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f131,f31])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 0.21/0.49    inference(superposition,[],[f123,f29])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f121,f32])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 0.21/0.49    inference(superposition,[],[f33,f30])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    ( ! [X47,X45,X46,X44] : (k3_enumset1(X44,X45,X44,X46,X47) = k2_xboole_0(k2_tarski(X44,X45),k2_tarski(X46,X47))) )),
% 0.21/0.49    inference(superposition,[],[f153,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 0.21/0.49    inference(superposition,[],[f25,f22])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).
% 0.21/0.49  fof(f285,plain,(
% 0.21/0.49    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2)),
% 0.21/0.49    inference(superposition,[],[f203,f183])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2))),
% 0.21/0.49    inference(forward_demodulation,[],[f202,f187])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_tarski(X3,X2)) )),
% 0.21/0.49    inference(superposition,[],[f168,f22])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f165,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) )),
% 0.21/0.49    inference(superposition,[],[f25,f22])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X0,X1,X1)) )),
% 0.21/0.49    inference(superposition,[],[f158,f28])).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2))),
% 0.21/0.49    inference(backward_demodulation,[],[f20,f187])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.49    inference(negated_conjecture,[],[f15])).
% 0.21/0.49  fof(f15,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (29390)------------------------------
% 0.21/0.49  % (29390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29390)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (29390)Memory used [KB]: 1791
% 0.21/0.49  % (29390)Time elapsed: 0.063 s
% 0.21/0.49  % (29390)------------------------------
% 0.21/0.49  % (29390)------------------------------
% 0.21/0.50  % (29386)Success in time 0.137 s
%------------------------------------------------------------------------------

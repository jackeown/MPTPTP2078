%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 213 expanded)
%              Number of leaves         :   11 (  71 expanded)
%              Depth                    :   17
%              Number of atoms          :   57 ( 214 expanded)
%              Number of equality atoms :   56 ( 213 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f471,plain,(
    $false ),
    inference(subsumption_resolution,[],[f470,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

fof(f470,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(superposition,[],[f469,f241])).

fof(f241,plain,(
    ! [X6,X8,X7] : k2_enumset1(X7,X6,X7,X8) = k1_enumset1(X6,X7,X8) ),
    inference(forward_demodulation,[],[f233,f240])).

fof(f240,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X1,X2) ),
    inference(forward_demodulation,[],[f232,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f232,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X1,X2) ),
    inference(superposition,[],[f229,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f229,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X2,X3) ),
    inference(forward_demodulation,[],[f226,f28])).

fof(f226,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X2,X3) ),
    inference(superposition,[],[f163,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f163,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X2,X3,X4,X0,X0,X1) = k3_enumset1(X2,X3,X4,X0,X1) ),
    inference(forward_demodulation,[],[f149,f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

fof(f149,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X2,X3,X4,X0,X0,X1) = k2_xboole_0(k1_enumset1(X2,X3,X4),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f32,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(f233,plain,(
    ! [X6,X8,X7] : k2_enumset1(X7,X6,X7,X8) = k2_enumset1(X6,X7,X7,X8) ),
    inference(superposition,[],[f229,f137])).

fof(f137,plain,(
    ! [X50,X48,X51,X49] : k3_enumset1(X48,X49,X49,X50,X51) = k2_enumset1(X49,X48,X50,X51) ),
    inference(forward_demodulation,[],[f133,f135])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f123,f28])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f30,f23])).

fof(f133,plain,(
    ! [X50,X48,X51,X49] : k3_enumset1(X48,X49,X49,X50,X51) = k2_xboole_0(k2_tarski(X49,X48),k2_tarski(X50,X51)) ),
    inference(superposition,[],[f30,f51])).

fof(f51,plain,(
    ! [X6,X5] : k1_enumset1(X6,X5,X5) = k2_tarski(X5,X6) ),
    inference(superposition,[],[f37,f25])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f26,f23])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

fof(f469,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2) ),
    inference(superposition,[],[f457,f135])).

fof(f457,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2)) ),
    inference(forward_demodulation,[],[f456,f437])).

fof(f437,plain,(
    ! [X19,X20] : k2_tarski(X19,X20) = k2_tarski(X20,X19) ),
    inference(superposition,[],[f396,f37])).

fof(f396,plain,(
    ! [X0,X1] : k2_tarski(X1,X0) = k1_enumset1(X0,X1,X0) ),
    inference(forward_demodulation,[],[f387,f51])).

fof(f387,plain,(
    ! [X0,X1] : k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1) ),
    inference(superposition,[],[f335,f27])).

fof(f335,plain,(
    ! [X2,X0,X1] : k1_enumset1(X1,X0,X2) = k2_enumset1(X1,X2,X0,X0) ),
    inference(backward_demodulation,[],[f167,f331])).

fof(f331,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X2,X1) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f320,f27])).

fof(f320,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k2_enumset1(X0,X0,X2,X1) ),
    inference(superposition,[],[f314,f23])).

fof(f314,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)) = k2_enumset1(X1,X2,X0,X3) ),
    inference(backward_demodulation,[],[f134,f308])).

fof(f308,plain,(
    ! [X50,X48,X51,X49] : k3_enumset1(X50,X51,X48,X49,X49) = k2_enumset1(X50,X51,X49,X48) ),
    inference(forward_demodulation,[],[f304,f135])).

fof(f304,plain,(
    ! [X50,X48,X51,X49] : k3_enumset1(X50,X51,X48,X49,X49) = k2_xboole_0(k2_tarski(X50,X51),k2_tarski(X49,X48)) ),
    inference(superposition,[],[f160,f51])).

fof(f160,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(forward_demodulation,[],[f138,f29])).

fof(f138,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(superposition,[],[f32,f23])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)) ),
    inference(superposition,[],[f30,f22])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f167,plain,(
    ! [X2,X0,X1] : k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) ),
    inference(superposition,[],[f135,f22])).

fof(f456,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2)) ),
    inference(backward_demodulation,[],[f21,f437])).

fof(f21,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:59:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (16434)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (16448)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (16435)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (16441)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.46  % (16447)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (16436)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (16439)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (16443)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (16433)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (16445)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (16440)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (16444)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (16438)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (16444)Refutation not found, incomplete strategy% (16444)------------------------------
% 0.21/0.48  % (16444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (16444)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (16444)Memory used [KB]: 10618
% 0.21/0.48  % (16444)Time elapsed: 0.062 s
% 0.21/0.48  % (16444)------------------------------
% 0.21/0.48  % (16444)------------------------------
% 0.21/0.48  % (16437)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (16449)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (16436)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f471,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f470,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).
% 0.21/0.48  fof(f470,plain,(
% 0.21/0.48    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 0.21/0.48    inference(superposition,[],[f469,f241])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    ( ! [X6,X8,X7] : (k2_enumset1(X7,X6,X7,X8) = k1_enumset1(X6,X7,X8)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f233,f240])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X1,X2)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f232,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X1,X2)) )),
% 0.21/0.48    inference(superposition,[],[f229,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X2,X3)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f226,f28])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X2,X3)) )),
% 0.21/0.48    inference(superposition,[],[f163,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X2,X3,X4,X0,X0,X1) = k3_enumset1(X2,X3,X4,X0,X1)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f149,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X2,X3,X4,X0,X0,X1) = k2_xboole_0(k1_enumset1(X2,X3,X4),k2_tarski(X0,X1))) )),
% 0.21/0.48    inference(superposition,[],[f32,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    ( ! [X6,X8,X7] : (k2_enumset1(X7,X6,X7,X8) = k2_enumset1(X6,X7,X7,X8)) )),
% 0.21/0.48    inference(superposition,[],[f229,f137])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ( ! [X50,X48,X51,X49] : (k3_enumset1(X48,X49,X49,X50,X51) = k2_enumset1(X49,X48,X50,X51)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f133,f135])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f123,f28])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.48    inference(superposition,[],[f30,f23])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ( ! [X50,X48,X51,X49] : (k3_enumset1(X48,X49,X49,X50,X51) = k2_xboole_0(k2_tarski(X49,X48),k2_tarski(X50,X51))) )),
% 0.21/0.48    inference(superposition,[],[f30,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X6,X5] : (k1_enumset1(X6,X5,X5) = k2_tarski(X5,X6)) )),
% 0.21/0.48    inference(superposition,[],[f37,f25])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 0.21/0.48    inference(superposition,[],[f26,f23])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).
% 0.21/0.48  fof(f469,plain,(
% 0.21/0.48    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2)),
% 0.21/0.48    inference(superposition,[],[f457,f135])).
% 0.21/0.48  fof(f457,plain,(
% 0.21/0.48    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2))),
% 0.21/0.48    inference(forward_demodulation,[],[f456,f437])).
% 0.21/0.48  fof(f437,plain,(
% 0.21/0.48    ( ! [X19,X20] : (k2_tarski(X19,X20) = k2_tarski(X20,X19)) )),
% 0.21/0.48    inference(superposition,[],[f396,f37])).
% 0.21/0.48  fof(f396,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X1,X0) = k1_enumset1(X0,X1,X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f387,f51])).
% 0.21/0.48  fof(f387,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)) )),
% 0.21/0.48    inference(superposition,[],[f335,f27])).
% 0.21/0.48  fof(f335,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X1,X0,X2) = k2_enumset1(X1,X2,X0,X0)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f167,f331])).
% 0.21/0.48  fof(f331,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X2,X1) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f320,f27])).
% 0.21/0.48  fof(f320,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k2_enumset1(X0,X0,X2,X1)) )),
% 0.21/0.48    inference(superposition,[],[f314,f23])).
% 0.21/0.48  fof(f314,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)) = k2_enumset1(X1,X2,X0,X3)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f134,f308])).
% 0.21/0.48  fof(f308,plain,(
% 0.21/0.48    ( ! [X50,X48,X51,X49] : (k3_enumset1(X50,X51,X48,X49,X49) = k2_enumset1(X50,X51,X49,X48)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f304,f135])).
% 0.21/0.48  fof(f304,plain,(
% 0.21/0.48    ( ! [X50,X48,X51,X49] : (k3_enumset1(X50,X51,X48,X49,X49) = k2_xboole_0(k2_tarski(X50,X51),k2_tarski(X49,X48))) )),
% 0.21/0.48    inference(superposition,[],[f160,f51])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f138,f29])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.21/0.48    inference(superposition,[],[f32,f23])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))) )),
% 0.21/0.48    inference(superposition,[],[f30,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) )),
% 0.21/0.48    inference(superposition,[],[f135,f22])).
% 0.21/0.48  fof(f456,plain,(
% 0.21/0.48    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2))),
% 0.21/0.48    inference(backward_demodulation,[],[f21,f437])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.48    inference(negated_conjecture,[],[f16])).
% 0.21/0.48  fof(f16,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (16436)------------------------------
% 0.21/0.48  % (16436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (16436)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (16436)Memory used [KB]: 2046
% 0.21/0.48  % (16436)Time elapsed: 0.069 s
% 0.21/0.48  % (16436)------------------------------
% 0.21/0.48  % (16436)------------------------------
% 0.21/0.48  % (16432)Success in time 0.131 s
%------------------------------------------------------------------------------

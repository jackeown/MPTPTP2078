%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:15 EST 2020

% Result     : Theorem 3.32s
% Output     : Refutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   36 (  40 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :   42 (  46 expanded)
%              Number of equality atoms :   35 (  39 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10104,plain,(
    $false ),
    inference(subsumption_resolution,[],[f17,f10103])).

fof(f10103,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k2_xboole_0(X5,X7),k3_xboole_0(X5,X6)) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X7,X5)) ),
    inference(backward_demodulation,[],[f881,f9793])).

fof(f9793,plain,(
    ! [X70,X72,X71] : k2_xboole_0(k4_xboole_0(X70,X71),k4_xboole_0(X72,k3_xboole_0(X70,X71))) = k2_xboole_0(k4_xboole_0(X70,X71),k4_xboole_0(X72,X70)) ),
    inference(superposition,[],[f803,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f803,plain,(
    ! [X12,X10,X11] : k2_xboole_0(X12,k4_xboole_0(X10,X11)) = k2_xboole_0(X12,k4_xboole_0(X10,k2_xboole_0(X11,X12))) ),
    inference(superposition,[],[f23,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f881,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k2_xboole_0(X5,X7),k3_xboole_0(X5,X6)) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X7,k3_xboole_0(X5,X6))) ),
    inference(superposition,[],[f28,f243])).

fof(f243,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f45,f224])).

fof(f224,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f55,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f55,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k3_xboole_0(k4_xboole_0(X5,X6),X5) ),
    inference(forward_demodulation,[],[f47,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f47,plain,(
    ! [X6,X5] : k3_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(k4_xboole_0(X5,X6),k1_xboole_0) ),
    inference(superposition,[],[f22,f30])).

fof(f30,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f26,f19])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f45,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f22,f22])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f17,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))
   => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (4623)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.44  % (4616)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (4624)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (4622)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (4622)Refutation not found, incomplete strategy% (4622)------------------------------
% 0.20/0.46  % (4622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (4622)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (4622)Memory used [KB]: 10490
% 0.20/0.46  % (4622)Time elapsed: 0.051 s
% 0.20/0.46  % (4622)------------------------------
% 0.20/0.46  % (4622)------------------------------
% 0.20/0.46  % (4614)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (4625)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (4615)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (4617)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (4621)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (4613)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (4611)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (4612)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.50  % (4628)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (4627)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.51  % (4620)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.51  % (4626)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.52  % (4619)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.37/0.52  % (4618)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 3.32/0.78  % (4627)Refutation found. Thanks to Tanya!
% 3.32/0.78  % SZS status Theorem for theBenchmark
% 3.32/0.78  % SZS output start Proof for theBenchmark
% 3.32/0.78  fof(f10104,plain,(
% 3.32/0.78    $false),
% 3.32/0.78    inference(subsumption_resolution,[],[f17,f10103])).
% 3.32/0.78  fof(f10103,plain,(
% 3.32/0.78    ( ! [X6,X7,X5] : (k4_xboole_0(k2_xboole_0(X5,X7),k3_xboole_0(X5,X6)) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X7,X5))) )),
% 3.32/0.78    inference(backward_demodulation,[],[f881,f9793])).
% 3.32/0.78  fof(f9793,plain,(
% 3.32/0.78    ( ! [X70,X72,X71] : (k2_xboole_0(k4_xboole_0(X70,X71),k4_xboole_0(X72,k3_xboole_0(X70,X71))) = k2_xboole_0(k4_xboole_0(X70,X71),k4_xboole_0(X72,X70))) )),
% 3.32/0.78    inference(superposition,[],[f803,f24])).
% 3.32/0.78  fof(f24,plain,(
% 3.32/0.78    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.32/0.78    inference(cnf_transformation,[],[f10])).
% 3.32/0.78  fof(f10,axiom,(
% 3.32/0.78    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.32/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 3.32/0.78  fof(f803,plain,(
% 3.32/0.78    ( ! [X12,X10,X11] : (k2_xboole_0(X12,k4_xboole_0(X10,X11)) = k2_xboole_0(X12,k4_xboole_0(X10,k2_xboole_0(X11,X12)))) )),
% 3.32/0.78    inference(superposition,[],[f23,f27])).
% 3.32/0.78  fof(f27,plain,(
% 3.32/0.78    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.32/0.78    inference(cnf_transformation,[],[f7])).
% 3.32/0.78  fof(f7,axiom,(
% 3.32/0.78    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.32/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 3.32/0.78  fof(f23,plain,(
% 3.32/0.78    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.32/0.78    inference(cnf_transformation,[],[f5])).
% 3.32/0.78  fof(f5,axiom,(
% 3.32/0.78    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.32/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 3.32/0.78  fof(f881,plain,(
% 3.32/0.78    ( ! [X6,X7,X5] : (k4_xboole_0(k2_xboole_0(X5,X7),k3_xboole_0(X5,X6)) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X7,k3_xboole_0(X5,X6)))) )),
% 3.32/0.78    inference(superposition,[],[f28,f243])).
% 3.32/0.78  fof(f243,plain,(
% 3.32/0.78    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 3.32/0.78    inference(backward_demodulation,[],[f45,f224])).
% 3.32/0.78  fof(f224,plain,(
% 3.32/0.78    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 3.32/0.78    inference(superposition,[],[f55,f20])).
% 3.32/0.78  fof(f20,plain,(
% 3.32/0.78    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.32/0.78    inference(cnf_transformation,[],[f2])).
% 3.32/0.78  fof(f2,axiom,(
% 3.32/0.78    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.32/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.32/0.78  fof(f55,plain,(
% 3.32/0.78    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k3_xboole_0(k4_xboole_0(X5,X6),X5)) )),
% 3.32/0.78    inference(forward_demodulation,[],[f47,f18])).
% 3.32/0.78  fof(f18,plain,(
% 3.32/0.78    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.32/0.78    inference(cnf_transformation,[],[f6])).
% 3.32/0.78  fof(f6,axiom,(
% 3.32/0.78    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.32/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 3.32/0.78  fof(f47,plain,(
% 3.32/0.78    ( ! [X6,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(k4_xboole_0(X5,X6),k1_xboole_0)) )),
% 3.32/0.78    inference(superposition,[],[f22,f30])).
% 3.32/0.78  fof(f30,plain,(
% 3.32/0.78    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 3.32/0.78    inference(resolution,[],[f26,f19])).
% 3.32/0.78  fof(f19,plain,(
% 3.32/0.78    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.32/0.78    inference(cnf_transformation,[],[f4])).
% 3.32/0.78  fof(f4,axiom,(
% 3.32/0.78    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.32/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.32/0.78  fof(f26,plain,(
% 3.32/0.78    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 3.32/0.78    inference(cnf_transformation,[],[f16])).
% 3.32/0.78  fof(f16,plain,(
% 3.32/0.78    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.32/0.78    inference(nnf_transformation,[],[f3])).
% 3.32/0.78  fof(f3,axiom,(
% 3.32/0.78    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.32/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.32/0.78  fof(f22,plain,(
% 3.32/0.78    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.32/0.78    inference(cnf_transformation,[],[f9])).
% 3.32/0.78  fof(f9,axiom,(
% 3.32/0.78    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.32/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.32/0.78  fof(f45,plain,(
% 3.32/0.78    ( ! [X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 3.32/0.78    inference(superposition,[],[f22,f22])).
% 3.32/0.78  fof(f28,plain,(
% 3.32/0.78    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 3.32/0.78    inference(cnf_transformation,[],[f8])).
% 3.32/0.78  fof(f8,axiom,(
% 3.32/0.78    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 3.32/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 3.32/0.78  fof(f17,plain,(
% 3.32/0.78    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 3.32/0.78    inference(cnf_transformation,[],[f15])).
% 3.32/0.78  fof(f15,plain,(
% 3.32/0.78    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 3.32/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 3.32/0.78  fof(f14,plain,(
% 3.32/0.78    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 3.32/0.78    introduced(choice_axiom,[])).
% 3.32/0.78  fof(f13,plain,(
% 3.32/0.78    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.32/0.78    inference(ennf_transformation,[],[f12])).
% 3.32/0.78  fof(f12,negated_conjecture,(
% 3.32/0.78    ~! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.32/0.78    inference(negated_conjecture,[],[f11])).
% 3.32/0.78  fof(f11,conjecture,(
% 3.32/0.78    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.32/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).
% 3.32/0.78  % SZS output end Proof for theBenchmark
% 3.32/0.78  % (4627)------------------------------
% 3.32/0.78  % (4627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.32/0.78  % (4627)Termination reason: Refutation
% 3.32/0.78  
% 3.32/0.78  % (4627)Memory used [KB]: 11001
% 3.32/0.78  % (4627)Time elapsed: 0.377 s
% 3.32/0.78  % (4627)------------------------------
% 3.32/0.78  % (4627)------------------------------
% 3.32/0.79  % (4609)Success in time 0.431 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:31:58 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 151 expanded)
%              Number of leaves         :   13 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :   66 ( 182 expanded)
%              Number of equality atoms :   53 ( 139 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1102,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1101])).

fof(f1101,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f982,f41])).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f27,f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f982,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f732,f970])).

fof(f970,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) ),
    inference(resolution,[],[f875,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f875,plain,(
    ! [X4,X2,X3] : r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X2,X3))) ),
    inference(superposition,[],[f852,f27])).

fof(f852,plain,(
    ! [X26,X27,X25] : r1_tarski(X26,k2_xboole_0(k2_xboole_0(X25,X26),X27)) ),
    inference(superposition,[],[f841,f210])).

fof(f210,plain,(
    ! [X10,X11] : k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11)) = X11 ),
    inference(forward_demodulation,[],[f209,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f209,plain,(
    ! [X10,X11] : k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11)) = k4_xboole_0(X11,k1_xboole_0) ),
    inference(forward_demodulation,[],[f179,f99])).

fof(f99,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f35,f52])).

fof(f52,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f34,f25])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f179,plain,(
    ! [X10,X11] : k4_xboole_0(X11,k4_xboole_0(X11,k2_xboole_0(X10,X11))) = k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11)) ),
    inference(superposition,[],[f38,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f26,f28,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f841,plain,(
    ! [X78,X76,X77] : r1_tarski(k4_xboole_0(X76,X77),k2_xboole_0(X76,X78)) ),
    inference(forward_demodulation,[],[f825,f23])).

fof(f825,plain,(
    ! [X78,X76,X77] : r1_tarski(k4_xboole_0(k4_xboole_0(X76,X77),k1_xboole_0),k2_xboole_0(X76,X78)) ),
    inference(superposition,[],[f193,f111])).

fof(f111,plain,(
    ! [X8,X7,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,X8),k2_xboole_0(X7,X9)) ),
    inference(forward_demodulation,[],[f96,f64])).

fof(f64,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5) ),
    inference(forward_demodulation,[],[f59,f53])).

fof(f53,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(resolution,[],[f34,f40])).

fof(f40,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f25,f23])).

fof(f59,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(X5,X5) ),
    inference(superposition,[],[f29,f41])).

fof(f96,plain,(
    ! [X8,X7,X9] : k4_xboole_0(k4_xboole_0(X7,X8),k2_xboole_0(X7,X9)) = k4_xboole_0(k1_xboole_0,X9) ),
    inference(superposition,[],[f35,f52])).

fof(f193,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) ),
    inference(superposition,[],[f25,f38])).

fof(f732,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f730,f35])).

fof(f730,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f606,f729])).

fof(f729,plain,(
    ! [X21,X19,X20] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X19,X20),X21),k2_xboole_0(X19,X20)) = k4_xboole_0(X21,k2_xboole_0(X19,X20)) ),
    inference(forward_demodulation,[],[f708,f41])).

fof(f708,plain,(
    ! [X21,X19,X20] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X19,X20),X21),k2_xboole_0(X19,X20)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X21,k2_xboole_0(X19,X20))) ),
    inference(superposition,[],[f36,f73])).

fof(f73,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f52,f29])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f606,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f604,f38])).

fof(f604,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) ),
    inference(backward_demodulation,[],[f37,f582])).

fof(f582,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(k4_xboole_0(X4,X5),X6)) ),
    inference(superposition,[],[f35,f210])).

fof(f37,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f21,f28,f30,f30])).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f21,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:50:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (29677)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (29676)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (29669)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (29672)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (29678)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (29679)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (29670)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (29674)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (29680)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (29683)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (29671)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (29673)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (29679)Refutation not found, incomplete strategy% (29679)------------------------------
% 0.21/0.50  % (29679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29679)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (29679)Memory used [KB]: 10490
% 0.21/0.50  % (29679)Time elapsed: 0.077 s
% 0.21/0.50  % (29679)------------------------------
% 0.21/0.50  % (29679)------------------------------
% 0.21/0.50  % (29667)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (29675)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.19/0.51  % (29669)Refutation found. Thanks to Tanya!
% 1.19/0.51  % SZS status Theorem for theBenchmark
% 1.19/0.51  % SZS output start Proof for theBenchmark
% 1.19/0.51  fof(f1102,plain,(
% 1.19/0.51    $false),
% 1.19/0.51    inference(trivial_inequality_removal,[],[f1101])).
% 1.19/0.51  fof(f1101,plain,(
% 1.19/0.51    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.19/0.51    inference(superposition,[],[f982,f41])).
% 1.19/0.51  fof(f41,plain,(
% 1.19/0.51    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.19/0.51    inference(superposition,[],[f27,f22])).
% 1.19/0.51  fof(f22,plain,(
% 1.19/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.19/0.51    inference(cnf_transformation,[],[f5])).
% 1.19/0.51  fof(f5,axiom,(
% 1.19/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.19/0.51  fof(f27,plain,(
% 1.19/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.19/0.51    inference(cnf_transformation,[],[f1])).
% 1.19/0.51  fof(f1,axiom,(
% 1.19/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.19/0.51  fof(f982,plain,(
% 1.19/0.51    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.19/0.51    inference(backward_demodulation,[],[f732,f970])).
% 1.19/0.51  fof(f970,plain,(
% 1.19/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0)))) )),
% 1.19/0.51    inference(resolution,[],[f875,f34])).
% 1.19/0.51  fof(f34,plain,(
% 1.19/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.19/0.51    inference(cnf_transformation,[],[f20])).
% 1.19/0.51  fof(f20,plain,(
% 1.19/0.51    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.19/0.51    inference(nnf_transformation,[],[f4])).
% 1.19/0.51  fof(f4,axiom,(
% 1.19/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.19/0.51  fof(f875,plain,(
% 1.19/0.51    ( ! [X4,X2,X3] : (r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X2,X3)))) )),
% 1.19/0.51    inference(superposition,[],[f852,f27])).
% 1.19/0.51  fof(f852,plain,(
% 1.19/0.51    ( ! [X26,X27,X25] : (r1_tarski(X26,k2_xboole_0(k2_xboole_0(X25,X26),X27))) )),
% 1.19/0.51    inference(superposition,[],[f841,f210])).
% 1.19/0.51  fof(f210,plain,(
% 1.19/0.51    ( ! [X10,X11] : (k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11)) = X11) )),
% 1.19/0.51    inference(forward_demodulation,[],[f209,f23])).
% 1.19/0.51  fof(f23,plain,(
% 1.19/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.19/0.51    inference(cnf_transformation,[],[f7])).
% 1.19/0.51  fof(f7,axiom,(
% 1.19/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.19/0.51  fof(f209,plain,(
% 1.19/0.51    ( ! [X10,X11] : (k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11)) = k4_xboole_0(X11,k1_xboole_0)) )),
% 1.19/0.51    inference(forward_demodulation,[],[f179,f99])).
% 1.19/0.51  fof(f99,plain,(
% 1.19/0.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 1.19/0.51    inference(superposition,[],[f35,f52])).
% 1.19/0.51  fof(f52,plain,(
% 1.19/0.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 1.19/0.51    inference(resolution,[],[f34,f25])).
% 1.19/0.51  fof(f25,plain,(
% 1.19/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.19/0.51    inference(cnf_transformation,[],[f6])).
% 1.19/0.51  fof(f6,axiom,(
% 1.19/0.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.19/0.51  fof(f35,plain,(
% 1.19/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.19/0.51    inference(cnf_transformation,[],[f9])).
% 1.19/0.51  fof(f9,axiom,(
% 1.19/0.51    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.19/0.51  fof(f179,plain,(
% 1.19/0.51    ( ! [X10,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,k2_xboole_0(X10,X11))) = k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11))) )),
% 1.19/0.51    inference(superposition,[],[f38,f29])).
% 1.19/0.51  fof(f29,plain,(
% 1.19/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.19/0.51    inference(cnf_transformation,[],[f8])).
% 1.19/0.51  fof(f8,axiom,(
% 1.19/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.19/0.51  fof(f38,plain,(
% 1.19/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.19/0.51    inference(definition_unfolding,[],[f26,f28,f28])).
% 1.19/0.51  fof(f28,plain,(
% 1.19/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.19/0.51    inference(cnf_transformation,[],[f11])).
% 1.19/0.51  fof(f11,axiom,(
% 1.19/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.19/0.51  fof(f26,plain,(
% 1.19/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.19/0.51    inference(cnf_transformation,[],[f2])).
% 1.19/0.51  fof(f2,axiom,(
% 1.19/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.19/0.51  fof(f841,plain,(
% 1.19/0.51    ( ! [X78,X76,X77] : (r1_tarski(k4_xboole_0(X76,X77),k2_xboole_0(X76,X78))) )),
% 1.19/0.51    inference(forward_demodulation,[],[f825,f23])).
% 1.19/0.51  fof(f825,plain,(
% 1.19/0.51    ( ! [X78,X76,X77] : (r1_tarski(k4_xboole_0(k4_xboole_0(X76,X77),k1_xboole_0),k2_xboole_0(X76,X78))) )),
% 1.19/0.51    inference(superposition,[],[f193,f111])).
% 1.19/0.51  fof(f111,plain,(
% 1.19/0.51    ( ! [X8,X7,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,X8),k2_xboole_0(X7,X9))) )),
% 1.19/0.51    inference(forward_demodulation,[],[f96,f64])).
% 1.19/0.51  fof(f64,plain,(
% 1.19/0.51    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)) )),
% 1.19/0.51    inference(forward_demodulation,[],[f59,f53])).
% 1.19/0.51  fof(f53,plain,(
% 1.19/0.51    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 1.19/0.51    inference(resolution,[],[f34,f40])).
% 1.19/0.51  fof(f40,plain,(
% 1.19/0.51    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.19/0.51    inference(superposition,[],[f25,f23])).
% 1.19/0.51  fof(f59,plain,(
% 1.19/0.51    ( ! [X5] : (k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(X5,X5)) )),
% 1.19/0.51    inference(superposition,[],[f29,f41])).
% 1.19/0.51  fof(f96,plain,(
% 1.19/0.51    ( ! [X8,X7,X9] : (k4_xboole_0(k4_xboole_0(X7,X8),k2_xboole_0(X7,X9)) = k4_xboole_0(k1_xboole_0,X9)) )),
% 1.19/0.51    inference(superposition,[],[f35,f52])).
% 1.19/0.51  fof(f193,plain,(
% 1.19/0.51    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)) )),
% 1.19/0.51    inference(superposition,[],[f25,f38])).
% 1.19/0.51  fof(f732,plain,(
% 1.19/0.51    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.19/0.51    inference(forward_demodulation,[],[f730,f35])).
% 1.19/0.51  fof(f730,plain,(
% 1.19/0.51    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.19/0.51    inference(backward_demodulation,[],[f606,f729])).
% 1.19/0.51  fof(f729,plain,(
% 1.19/0.51    ( ! [X21,X19,X20] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X19,X20),X21),k2_xboole_0(X19,X20)) = k4_xboole_0(X21,k2_xboole_0(X19,X20))) )),
% 1.19/0.51    inference(forward_demodulation,[],[f708,f41])).
% 1.19/0.51  fof(f708,plain,(
% 1.19/0.51    ( ! [X21,X19,X20] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X19,X20),X21),k2_xboole_0(X19,X20)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X21,k2_xboole_0(X19,X20)))) )),
% 1.19/0.51    inference(superposition,[],[f36,f73])).
% 1.19/0.51  fof(f73,plain,(
% 1.19/0.51    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(X2,X3))) )),
% 1.19/0.51    inference(superposition,[],[f52,f29])).
% 1.19/0.51  fof(f36,plain,(
% 1.19/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 1.19/0.51    inference(cnf_transformation,[],[f10])).
% 1.19/0.51  fof(f10,axiom,(
% 1.19/0.51    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 1.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 1.19/0.51  fof(f606,plain,(
% 1.19/0.51    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.19/0.51    inference(forward_demodulation,[],[f604,f38])).
% 1.19/0.51  fof(f604,plain,(
% 1.19/0.51    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))),
% 1.19/0.51    inference(backward_demodulation,[],[f37,f582])).
% 1.19/0.51  fof(f582,plain,(
% 1.19/0.51    ( ! [X6,X4,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(k4_xboole_0(X4,X5),X6))) )),
% 1.19/0.51    inference(superposition,[],[f35,f210])).
% 1.19/0.51  fof(f37,plain,(
% 1.19/0.51    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 1.19/0.51    inference(definition_unfolding,[],[f21,f28,f30,f30])).
% 1.19/0.51  fof(f30,plain,(
% 1.19/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.19/0.51    inference(cnf_transformation,[],[f3])).
% 1.19/0.51  fof(f3,axiom,(
% 1.19/0.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 1.19/0.51  fof(f21,plain,(
% 1.19/0.51    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 1.19/0.51    inference(cnf_transformation,[],[f18])).
% 1.19/0.51  fof(f18,plain,(
% 1.19/0.51    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 1.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 1.19/0.51  fof(f17,plain,(
% 1.19/0.51    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 1.19/0.51    introduced(choice_axiom,[])).
% 1.19/0.51  fof(f16,plain,(
% 1.19/0.51    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.19/0.51    inference(ennf_transformation,[],[f15])).
% 1.19/0.51  fof(f15,negated_conjecture,(
% 1.19/0.51    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.19/0.51    inference(negated_conjecture,[],[f14])).
% 1.19/0.51  fof(f14,conjecture,(
% 1.19/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.19/0.51  % SZS output end Proof for theBenchmark
% 1.19/0.51  % (29669)------------------------------
% 1.19/0.51  % (29669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.51  % (29669)Termination reason: Refutation
% 1.19/0.51  
% 1.19/0.51  % (29669)Memory used [KB]: 2302
% 1.19/0.51  % (29669)Time elapsed: 0.079 s
% 1.19/0.51  % (29669)------------------------------
% 1.19/0.51  % (29669)------------------------------
% 1.19/0.51  % (29684)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.19/0.51  % (29662)Success in time 0.146 s
%------------------------------------------------------------------------------

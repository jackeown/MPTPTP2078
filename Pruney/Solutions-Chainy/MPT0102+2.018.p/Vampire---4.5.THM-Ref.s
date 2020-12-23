%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 690 expanded)
%              Number of leaves         :   13 ( 230 expanded)
%              Depth                    :   27
%              Number of atoms          :   77 ( 691 expanded)
%              Number of equality atoms :   76 ( 690 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1989,plain,(
    $false ),
    inference(subsumption_resolution,[],[f17,f1984])).

fof(f1984,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k5_xboole_0(k5_xboole_0(X8,X9),k2_xboole_0(X8,X9)) ),
    inference(backward_demodulation,[],[f696,f1981])).

fof(f1981,plain,(
    ! [X33,X34] : k3_xboole_0(X33,X34) = k3_xboole_0(k2_xboole_0(X33,X34),k3_xboole_0(X33,X34)) ),
    inference(forward_demodulation,[],[f1930,f20])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f1930,plain,(
    ! [X33,X34] : k3_xboole_0(k2_xboole_0(X33,X34),k3_xboole_0(X33,X34)) = k4_xboole_0(k3_xboole_0(X33,X34),k1_xboole_0) ),
    inference(superposition,[],[f1897,f651])).

fof(f651,plain,(
    ! [X10,X11] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X10,X11),k2_xboole_0(X10,X11)) ),
    inference(superposition,[],[f621,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f621,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f614,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f614,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f597,f403])).

fof(f403,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f394,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f394,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f381,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f381,plain,(
    ! [X5] : k2_xboole_0(k4_xboole_0(k1_xboole_0,X5),X5) = X5 ),
    inference(forward_demodulation,[],[f365,f174])).

fof(f174,plain,(
    ! [X7] : k5_xboole_0(k1_xboole_0,X7) = X7 ),
    inference(forward_demodulation,[],[f136,f154])).

fof(f154,plain,(
    ! [X0] : k4_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(backward_demodulation,[],[f85,f152])).

fof(f152,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(backward_demodulation,[],[f40,f151])).

fof(f151,plain,(
    ! [X0] : k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(forward_demodulation,[],[f131,f18])).

fof(f18,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f131,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f25,f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f23,f37])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f23,f20])).

fof(f85,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f40,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f136,plain,(
    ! [X7] : k5_xboole_0(k1_xboole_0,X7) = k4_xboole_0(X7,k3_xboole_0(k1_xboole_0,X7)) ),
    inference(superposition,[],[f25,f29])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f22,f19])).

fof(f365,plain,(
    ! [X5] : k5_xboole_0(k1_xboole_0,X5) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X5),X5) ),
    inference(superposition,[],[f26,f20])).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f597,plain,(
    ! [X0,X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f28,f436])).

fof(f436,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f37,f430])).

fof(f430,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f265,f417])).

fof(f417,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f403,f23])).

fof(f265,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f162,f21])).

fof(f162,plain,(
    ! [X2] : k3_xboole_0(X2,k1_xboole_0) = k3_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f155,f37])).

fof(f155,plain,(
    ! [X2] : k3_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(X2,X2) ),
    inference(backward_demodulation,[],[f90,f152])).

fof(f90,plain,(
    ! [X2] : k3_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(X2,k3_xboole_0(X2,X2)) ),
    inference(superposition,[],[f23,f40])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1897,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X2,X1) ),
    inference(forward_demodulation,[],[f1876,f1380])).

fof(f1380,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f728,f21])).

fof(f728,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k3_xboole_0(k3_xboole_0(X1,X2),X2) ),
    inference(forward_demodulation,[],[f720,f20])).

fof(f720,plain,(
    ! [X2,X1] : k3_xboole_0(k3_xboole_0(X1,X2),X2) = k4_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0) ),
    inference(superposition,[],[f23,f625])).

fof(f625,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X8,X9),X9) ),
    inference(superposition,[],[f614,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f24,f21])).

fof(f1876,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f23,f1728])).

fof(f1728,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f1665,f21])).

fof(f1665,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(backward_demodulation,[],[f38,f1644])).

fof(f1644,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f770,f21])).

fof(f770,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f762,f20])).

fof(f762,plain,(
    ! [X2,X3] : k3_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0) ),
    inference(superposition,[],[f23,f649])).

fof(f649,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X7),X6) ),
    inference(superposition,[],[f621,f24])).

fof(f38,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f23,f23])).

fof(f696,plain,(
    ! [X8,X9] : k3_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(X8,X9)) = k5_xboole_0(k5_xboole_0(X8,X9),k2_xboole_0(X8,X9)) ),
    inference(superposition,[],[f639,f25])).

fof(f639,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k5_xboole_0(k4_xboole_0(X3,X4),X3) ),
    inference(forward_demodulation,[],[f637,f29])).

fof(f637,plain,(
    ! [X4,X3] : k5_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X3,X4)) ),
    inference(backward_demodulation,[],[f380,f621])).

fof(f380,plain,(
    ! [X4,X3] : k5_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X4,X3)),k3_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f364,f28])).

fof(f364,plain,(
    ! [X4,X3] : k5_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X3,X4),X3),k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f26,f23])).

fof(f17,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:41:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (28587)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (28584)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (28583)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (28582)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (28594)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (28592)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (28590)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (28592)Refutation not found, incomplete strategy% (28592)------------------------------
% 0.22/0.49  % (28592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (28592)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (28592)Memory used [KB]: 10490
% 0.22/0.49  % (28592)Time elapsed: 0.071 s
% 0.22/0.49  % (28592)------------------------------
% 0.22/0.49  % (28592)------------------------------
% 0.22/0.49  % (28591)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (28596)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  % (28585)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (28588)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (28589)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.51  % (28597)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (28581)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (28593)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (28595)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.52  % (28586)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.52  % (28598)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.58  % (28597)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f1989,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(subsumption_resolution,[],[f17,f1984])).
% 0.22/0.58  fof(f1984,plain,(
% 0.22/0.58    ( ! [X8,X9] : (k3_xboole_0(X8,X9) = k5_xboole_0(k5_xboole_0(X8,X9),k2_xboole_0(X8,X9))) )),
% 0.22/0.58    inference(backward_demodulation,[],[f696,f1981])).
% 0.22/0.58  fof(f1981,plain,(
% 0.22/0.58    ( ! [X33,X34] : (k3_xboole_0(X33,X34) = k3_xboole_0(k2_xboole_0(X33,X34),k3_xboole_0(X33,X34))) )),
% 0.22/0.58    inference(forward_demodulation,[],[f1930,f20])).
% 0.22/0.58  fof(f20,plain,(
% 0.22/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f6])).
% 0.22/0.58  fof(f6,axiom,(
% 0.22/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.58  fof(f1930,plain,(
% 0.22/0.58    ( ! [X33,X34] : (k3_xboole_0(k2_xboole_0(X33,X34),k3_xboole_0(X33,X34)) = k4_xboole_0(k3_xboole_0(X33,X34),k1_xboole_0)) )),
% 0.22/0.58    inference(superposition,[],[f1897,f651])).
% 0.22/0.58  fof(f651,plain,(
% 0.22/0.58    ( ! [X10,X11] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X10,X11),k2_xboole_0(X10,X11))) )),
% 0.22/0.58    inference(superposition,[],[f621,f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f11])).
% 0.22/0.58  fof(f11,axiom,(
% 0.22/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 0.22/0.58  fof(f621,plain,(
% 0.22/0.58    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 0.22/0.58    inference(superposition,[],[f614,f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.58  fof(f614,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.58    inference(forward_demodulation,[],[f597,f403])).
% 0.22/0.58  fof(f403,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f394,f24])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f9])).
% 0.22/0.58  fof(f9,axiom,(
% 0.22/0.58    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.58  fof(f394,plain,(
% 0.22/0.58    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) )),
% 0.22/0.58    inference(superposition,[],[f381,f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,axiom,(
% 0.22/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.58  fof(f381,plain,(
% 0.22/0.58    ( ! [X5] : (k2_xboole_0(k4_xboole_0(k1_xboole_0,X5),X5) = X5) )),
% 0.22/0.58    inference(forward_demodulation,[],[f365,f174])).
% 0.22/0.58  fof(f174,plain,(
% 0.22/0.58    ( ! [X7] : (k5_xboole_0(k1_xboole_0,X7) = X7) )),
% 0.22/0.58    inference(forward_demodulation,[],[f136,f154])).
% 0.22/0.58  fof(f154,plain,(
% 0.22/0.58    ( ! [X0] : (k4_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0) )),
% 0.22/0.58    inference(backward_demodulation,[],[f85,f152])).
% 0.22/0.58  fof(f152,plain,(
% 0.22/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.58    inference(backward_demodulation,[],[f40,f151])).
% 0.22/0.58  fof(f151,plain,(
% 0.22/0.58    ( ! [X0] : (k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.22/0.58    inference(forward_demodulation,[],[f131,f18])).
% 0.22/0.58  fof(f18,plain,(
% 0.22/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f10])).
% 0.22/0.58  fof(f10,axiom,(
% 0.22/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.58  fof(f131,plain,(
% 0.22/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.58    inference(superposition,[],[f25,f19])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.58    inference(superposition,[],[f23,f37])).
% 0.22/0.58  fof(f37,plain,(
% 0.22/0.58    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.22/0.58    inference(superposition,[],[f23,f20])).
% 0.22/0.58  fof(f85,plain,(
% 0.22/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) )),
% 0.22/0.58    inference(superposition,[],[f40,f21])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.58  fof(f136,plain,(
% 0.22/0.58    ( ! [X7] : (k5_xboole_0(k1_xboole_0,X7) = k4_xboole_0(X7,k3_xboole_0(k1_xboole_0,X7))) )),
% 0.22/0.58    inference(superposition,[],[f25,f29])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.22/0.58    inference(superposition,[],[f22,f19])).
% 0.22/0.58  fof(f365,plain,(
% 0.22/0.58    ( ! [X5] : (k5_xboole_0(k1_xboole_0,X5) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X5),X5)) )),
% 0.22/0.58    inference(superposition,[],[f26,f20])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.22/0.58  fof(f597,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.58    inference(superposition,[],[f28,f436])).
% 0.22/0.58  fof(f436,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.58    inference(backward_demodulation,[],[f37,f430])).
% 0.22/0.58  fof(f430,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.58    inference(backward_demodulation,[],[f265,f417])).
% 0.22/0.58  fof(f417,plain,(
% 0.22/0.58    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 0.22/0.58    inference(superposition,[],[f403,f23])).
% 0.22/0.58  fof(f265,plain,(
% 0.22/0.58    ( ! [X0] : (k3_xboole_0(k1_xboole_0,X0) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) )),
% 0.22/0.58    inference(superposition,[],[f162,f21])).
% 0.22/0.58  fof(f162,plain,(
% 0.22/0.58    ( ! [X2] : (k3_xboole_0(X2,k1_xboole_0) = k3_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0))) )),
% 0.22/0.58    inference(forward_demodulation,[],[f155,f37])).
% 0.22/0.58  fof(f155,plain,(
% 0.22/0.58    ( ! [X2] : (k3_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(X2,X2)) )),
% 0.22/0.58    inference(backward_demodulation,[],[f90,f152])).
% 0.22/0.58  fof(f90,plain,(
% 0.22/0.58    ( ! [X2] : (k3_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(X2,k3_xboole_0(X2,X2))) )),
% 0.22/0.58    inference(superposition,[],[f23,f40])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f7])).
% 0.22/0.58  fof(f7,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.58  fof(f1897,plain,(
% 0.22/0.58    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X2,X1)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f1876,f1380])).
% 0.22/0.58  fof(f1380,plain,(
% 0.22/0.58    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4))) )),
% 0.22/0.58    inference(superposition,[],[f728,f21])).
% 0.22/0.58  fof(f728,plain,(
% 0.22/0.58    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k3_xboole_0(k3_xboole_0(X1,X2),X2)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f720,f20])).
% 0.22/0.58  fof(f720,plain,(
% 0.22/0.58    ( ! [X2,X1] : (k3_xboole_0(k3_xboole_0(X1,X2),X2) = k4_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0)) )),
% 0.22/0.58    inference(superposition,[],[f23,f625])).
% 0.22/0.58  fof(f625,plain,(
% 0.22/0.58    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X8,X9),X9)) )),
% 0.22/0.58    inference(superposition,[],[f614,f42])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.58    inference(superposition,[],[f24,f21])).
% 0.22/0.58  fof(f1876,plain,(
% 0.22/0.58    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 0.22/0.58    inference(superposition,[],[f23,f1728])).
% 0.22/0.58  fof(f1728,plain,(
% 0.22/0.58    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 0.22/0.58    inference(superposition,[],[f1665,f21])).
% 0.22/0.58  fof(f1665,plain,(
% 0.22/0.58    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 0.22/0.58    inference(backward_demodulation,[],[f38,f1644])).
% 0.22/0.58  fof(f1644,plain,(
% 0.22/0.58    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 0.22/0.58    inference(superposition,[],[f770,f21])).
% 0.22/0.58  fof(f770,plain,(
% 0.22/0.58    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f762,f20])).
% 0.22/0.58  fof(f762,plain,(
% 0.22/0.58    ( ! [X2,X3] : (k3_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0)) )),
% 0.22/0.58    inference(superposition,[],[f23,f649])).
% 0.22/0.58  fof(f649,plain,(
% 0.22/0.58    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X7),X6)) )),
% 0.22/0.58    inference(superposition,[],[f621,f24])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 0.22/0.58    inference(superposition,[],[f23,f23])).
% 0.22/0.58  fof(f696,plain,(
% 0.22/0.58    ( ! [X8,X9] : (k3_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(X8,X9)) = k5_xboole_0(k5_xboole_0(X8,X9),k2_xboole_0(X8,X9))) )),
% 0.22/0.58    inference(superposition,[],[f639,f25])).
% 0.22/0.58  fof(f639,plain,(
% 0.22/0.58    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k5_xboole_0(k4_xboole_0(X3,X4),X3)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f637,f29])).
% 0.22/0.58  fof(f637,plain,(
% 0.22/0.58    ( ! [X4,X3] : (k5_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X3,X4))) )),
% 0.22/0.58    inference(backward_demodulation,[],[f380,f621])).
% 0.22/0.58  fof(f380,plain,(
% 0.22/0.58    ( ! [X4,X3] : (k5_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X4,X3)),k3_xboole_0(X3,X4))) )),
% 0.22/0.58    inference(forward_demodulation,[],[f364,f28])).
% 0.22/0.58  fof(f364,plain,(
% 0.22/0.58    ( ! [X4,X3] : (k5_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X3,X4),X3),k3_xboole_0(X3,X4))) )),
% 0.22/0.58    inference(superposition,[],[f26,f23])).
% 0.22/0.58  fof(f17,plain,(
% 0.22/0.58    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.22/0.58    inference(cnf_transformation,[],[f16])).
% 0.22/0.58  fof(f16,plain,(
% 0.22/0.58    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 0.22/0.58  fof(f15,plain,(
% 0.22/0.58    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f14,plain,(
% 0.22/0.58    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f13])).
% 0.22/0.58  fof(f13,negated_conjecture,(
% 0.22/0.58    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.22/0.58    inference(negated_conjecture,[],[f12])).
% 0.22/0.58  fof(f12,conjecture,(
% 0.22/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (28597)------------------------------
% 0.22/0.58  % (28597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (28597)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (28597)Memory used [KB]: 7419
% 0.22/0.58  % (28597)Time elapsed: 0.150 s
% 0.22/0.58  % (28597)------------------------------
% 0.22/0.58  % (28597)------------------------------
% 0.22/0.58  % (28580)Success in time 0.215 s
%------------------------------------------------------------------------------

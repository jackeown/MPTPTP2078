%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  61 expanded)
%              Number of leaves         :    6 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :   34 (  62 expanded)
%              Number of equality atoms :   33 (  61 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f463,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f455])).

fof(f455,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f23,f357])).

fof(f357,plain,(
    ! [X6,X8,X7] : k3_xboole_0(X6,k4_xboole_0(X7,X8)) = k3_xboole_0(X6,k4_xboole_0(X7,k3_xboole_0(X6,X8))) ),
    inference(forward_demodulation,[],[f321,f69])).

fof(f69,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k3_xboole_0(X5,k3_xboole_0(X3,X4))) = k4_xboole_0(X3,k3_xboole_0(X5,X4)) ),
    inference(forward_demodulation,[],[f61,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f61,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k3_xboole_0(X5,k3_xboole_0(X3,X4))) = k2_xboole_0(k4_xboole_0(X3,X5),k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f16,f13])).

fof(f13,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f321,plain,(
    ! [X6,X8,X7] : k3_xboole_0(X6,k4_xboole_0(X7,X8)) = k3_xboole_0(X6,k4_xboole_0(X7,k3_xboole_0(X6,k3_xboole_0(X7,X8)))) ),
    inference(backward_demodulation,[],[f28,f317])).

fof(f317,plain,(
    ! [X14,X12,X13] : k3_xboole_0(k3_xboole_0(X12,X13),X14) = k3_xboole_0(X12,k3_xboole_0(X13,X14)) ),
    inference(forward_demodulation,[],[f281,f151])).

fof(f151,plain,(
    ! [X21,X19,X20] : k3_xboole_0(X19,k3_xboole_0(k3_xboole_0(X19,X20),X21)) = k3_xboole_0(X19,k3_xboole_0(X20,X21)) ),
    inference(forward_demodulation,[],[f137,f12])).

fof(f12,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f137,plain,(
    ! [X21,X19,X20] : k3_xboole_0(X19,k3_xboole_0(k3_xboole_0(X19,X20),X21)) = k4_xboole_0(X19,k4_xboole_0(X19,k3_xboole_0(X20,X21))) ),
    inference(superposition,[],[f12,f64])).

fof(f64,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k3_xboole_0(k3_xboole_0(X3,X4),X5)) = k4_xboole_0(X3,k3_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f57,f16])).

fof(f57,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k3_xboole_0(k3_xboole_0(X3,X4),X5)) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,X5)) ),
    inference(superposition,[],[f16,f13])).

fof(f281,plain,(
    ! [X14,X12,X13] : k3_xboole_0(k3_xboole_0(X12,X13),X14) = k3_xboole_0(X12,k3_xboole_0(k3_xboole_0(X12,X13),X14)) ),
    inference(superposition,[],[f20,f27])).

fof(f27,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k3_xboole_0(X3,X4),X5) = k3_xboole_0(X3,k4_xboole_0(X4,k3_xboole_0(X3,k4_xboole_0(X4,X5)))) ),
    inference(forward_demodulation,[],[f21,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f21,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k3_xboole_0(X3,X4),X5) = k3_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(k3_xboole_0(X3,X4),X5))) ),
    inference(superposition,[],[f14,f12])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f19,f12])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f12,f13])).

fof(f28,plain,(
    ! [X6,X8,X7] : k3_xboole_0(X6,k4_xboole_0(X7,k3_xboole_0(k3_xboole_0(X6,X7),X8))) = k3_xboole_0(X6,k4_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f22,f14])).

fof(f22,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k3_xboole_0(X6,X7),X8) = k3_xboole_0(X6,k4_xboole_0(X7,k3_xboole_0(k3_xboole_0(X6,X7),X8))) ),
    inference(superposition,[],[f14,f13])).

fof(f23,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK2))) ),
    inference(superposition,[],[f11,f14])).

fof(f11,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (27465)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.45  % (27453)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (27452)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (27451)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (27462)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (27459)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (27461)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (27453)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f463,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f455])).
% 0.21/0.47  fof(f455,plain,(
% 0.21/0.47    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.47    inference(superposition,[],[f23,f357])).
% 0.21/0.47  fof(f357,plain,(
% 0.21/0.47    ( ! [X6,X8,X7] : (k3_xboole_0(X6,k4_xboole_0(X7,X8)) = k3_xboole_0(X6,k4_xboole_0(X7,k3_xboole_0(X6,X8)))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f321,f69])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k3_xboole_0(X5,k3_xboole_0(X3,X4))) = k4_xboole_0(X3,k3_xboole_0(X5,X4))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f61,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k3_xboole_0(X5,k3_xboole_0(X3,X4))) = k2_xboole_0(k4_xboole_0(X3,X5),k4_xboole_0(X3,X4))) )),
% 0.21/0.47    inference(superposition,[],[f16,f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.47  fof(f321,plain,(
% 0.21/0.47    ( ! [X6,X8,X7] : (k3_xboole_0(X6,k4_xboole_0(X7,X8)) = k3_xboole_0(X6,k4_xboole_0(X7,k3_xboole_0(X6,k3_xboole_0(X7,X8))))) )),
% 0.21/0.47    inference(backward_demodulation,[],[f28,f317])).
% 0.21/0.47  fof(f317,plain,(
% 0.21/0.47    ( ! [X14,X12,X13] : (k3_xboole_0(k3_xboole_0(X12,X13),X14) = k3_xboole_0(X12,k3_xboole_0(X13,X14))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f281,f151])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    ( ! [X21,X19,X20] : (k3_xboole_0(X19,k3_xboole_0(k3_xboole_0(X19,X20),X21)) = k3_xboole_0(X19,k3_xboole_0(X20,X21))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f137,f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    ( ! [X21,X19,X20] : (k3_xboole_0(X19,k3_xboole_0(k3_xboole_0(X19,X20),X21)) = k4_xboole_0(X19,k4_xboole_0(X19,k3_xboole_0(X20,X21)))) )),
% 0.21/0.47    inference(superposition,[],[f12,f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k3_xboole_0(k3_xboole_0(X3,X4),X5)) = k4_xboole_0(X3,k3_xboole_0(X4,X5))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f57,f16])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k3_xboole_0(k3_xboole_0(X3,X4),X5)) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,X5))) )),
% 0.21/0.47    inference(superposition,[],[f16,f13])).
% 0.21/0.47  fof(f281,plain,(
% 0.21/0.47    ( ! [X14,X12,X13] : (k3_xboole_0(k3_xboole_0(X12,X13),X14) = k3_xboole_0(X12,k3_xboole_0(k3_xboole_0(X12,X13),X14))) )),
% 0.21/0.47    inference(superposition,[],[f20,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (k3_xboole_0(k3_xboole_0(X3,X4),X5) = k3_xboole_0(X3,k4_xboole_0(X4,k3_xboole_0(X3,k4_xboole_0(X4,X5))))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f21,f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (k3_xboole_0(k3_xboole_0(X3,X4),X5) = k3_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(k3_xboole_0(X3,X4),X5)))) )),
% 0.21/0.47    inference(superposition,[],[f14,f12])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f19,f12])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(superposition,[],[f12,f13])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X6,X8,X7] : (k3_xboole_0(X6,k4_xboole_0(X7,k3_xboole_0(k3_xboole_0(X6,X7),X8))) = k3_xboole_0(X6,k4_xboole_0(X7,X8))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f22,f14])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X6,X8,X7] : (k4_xboole_0(k3_xboole_0(X6,X7),X8) = k3_xboole_0(X6,k4_xboole_0(X7,k3_xboole_0(k3_xboole_0(X6,X7),X8)))) )),
% 0.21/0.47    inference(superposition,[],[f14,f13])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK2)))),
% 0.21/0.47    inference(superposition,[],[f11,f14])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) => k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (27453)------------------------------
% 0.21/0.47  % (27453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (27453)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (27453)Memory used [KB]: 2046
% 0.21/0.47  % (27453)Time elapsed: 0.041 s
% 0.21/0.47  % (27453)------------------------------
% 0.21/0.47  % (27453)------------------------------
% 0.21/0.48  % (27461)Refutation not found, incomplete strategy% (27461)------------------------------
% 0.21/0.48  % (27461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27461)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (27461)Memory used [KB]: 10490
% 0.21/0.48  % (27461)Time elapsed: 0.058 s
% 0.21/0.48  % (27461)------------------------------
% 0.21/0.48  % (27461)------------------------------
% 0.21/0.48  % (27449)Success in time 0.117 s
%------------------------------------------------------------------------------

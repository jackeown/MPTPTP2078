%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   36 (  79 expanded)
%              Number of leaves         :    9 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :   37 (  80 expanded)
%              Number of equality atoms :   36 (  79 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f485,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f478])).

fof(f478,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    inference(superposition,[],[f15,f468])).

fof(f468,plain,(
    ! [X26,X24,X23,X21,X25,X22,X20] : k5_enumset1(X25,X26,X20,X21,X22,X23,X24) = k2_xboole_0(k4_enumset1(X25,X26,X20,X21,X22,X23),k1_tarski(X24)) ),
    inference(forward_demodulation,[],[f458,f182])).

fof(f182,plain,(
    ! [X26,X24,X23,X21,X25,X22,X20] : k2_xboole_0(k2_tarski(X25,X26),k3_enumset1(X20,X21,X22,X23,X24)) = k5_enumset1(X25,X26,X20,X21,X22,X23,X24) ),
    inference(forward_demodulation,[],[f180,f24])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_enumset1)).

fof(f180,plain,(
    ! [X26,X24,X23,X21,X25,X22,X20] : k2_xboole_0(k2_enumset1(X25,X26,X20,X21),k1_enumset1(X22,X23,X24)) = k2_xboole_0(k2_tarski(X25,X26),k3_enumset1(X20,X21,X22,X23,X24)) ),
    inference(superposition,[],[f81,f148])).

fof(f148,plain,(
    ! [X14,X17,X15,X18,X16] : k2_xboole_0(k2_tarski(X17,X18),k1_enumset1(X14,X15,X16)) = k3_enumset1(X17,X18,X14,X15,X16) ),
    inference(forward_demodulation,[],[f141,f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f141,plain,(
    ! [X14,X17,X15,X18,X16] : k2_xboole_0(k2_enumset1(X17,X18,X14,X15),k1_tarski(X16)) = k2_xboole_0(k2_tarski(X17,X18),k1_enumset1(X14,X15,X16)) ),
    inference(superposition,[],[f81,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f81,plain,(
    ! [X14,X17,X15,X18,X16] : k2_xboole_0(k2_tarski(X16,X17),k2_xboole_0(k2_tarski(X14,X15),X18)) = k2_xboole_0(k2_enumset1(X16,X17,X14,X15),X18) ),
    inference(forward_demodulation,[],[f72,f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f72,plain,(
    ! [X14,X17,X15,X18,X16] : k2_xboole_0(k2_xboole_0(k1_enumset1(X16,X17,X14),k1_tarski(X15)),X18) = k2_xboole_0(k2_tarski(X16,X17),k2_xboole_0(k2_tarski(X14,X15),X18)) ),
    inference(superposition,[],[f27,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f27,plain,(
    ! [X6,X4,X8,X7,X5] : k2_xboole_0(k2_tarski(X4,X5),k2_xboole_0(k2_xboole_0(k1_tarski(X6),X7),X8)) = k2_xboole_0(k2_xboole_0(k1_enumset1(X4,X5,X6),X7),X8) ),
    inference(superposition,[],[f20,f18])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_xboole_1)).

fof(f458,plain,(
    ! [X26,X24,X23,X21,X25,X22,X20] : k2_xboole_0(k2_tarski(X25,X26),k3_enumset1(X20,X21,X22,X23,X24)) = k2_xboole_0(k4_enumset1(X25,X26,X20,X21,X22,X23),k1_tarski(X24)) ),
    inference(superposition,[],[f200,f21])).

fof(f200,plain,(
    ! [X24,X23,X21,X19,X22,X20,X18] : k2_xboole_0(k2_tarski(X20,X21),k2_xboole_0(k2_enumset1(X22,X23,X18,X19),X24)) = k2_xboole_0(k4_enumset1(X20,X21,X22,X23,X18,X19),X24) ),
    inference(forward_demodulation,[],[f199,f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(f199,plain,(
    ! [X24,X23,X21,X19,X22,X20,X18] : k2_xboole_0(k2_xboole_0(k3_enumset1(X20,X21,X22,X23,X18),k1_tarski(X19)),X24) = k2_xboole_0(k2_tarski(X20,X21),k2_xboole_0(k2_enumset1(X22,X23,X18,X19),X24)) ),
    inference(forward_demodulation,[],[f186,f140])).

fof(f140,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k2_xboole_0(k2_enumset1(X12,X13,X7,X8),k2_xboole_0(k2_tarski(X9,X10),X11)) = k2_xboole_0(k2_tarski(X12,X13),k2_xboole_0(k2_enumset1(X7,X8,X9,X10),X11)) ),
    inference(superposition,[],[f81,f81])).

fof(f186,plain,(
    ! [X24,X23,X21,X19,X22,X20,X18] : k2_xboole_0(k2_xboole_0(k3_enumset1(X20,X21,X22,X23,X18),k1_tarski(X19)),X24) = k2_xboole_0(k2_enumset1(X20,X21,X22,X23),k2_xboole_0(k2_tarski(X18,X19),X24)) ),
    inference(superposition,[],[f33,f16])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k2_xboole_0(k1_tarski(X4),X5),X6)) = k2_xboole_0(k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5),X6) ),
    inference(superposition,[],[f20,f21])).

fof(f15,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:45:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.44  % (22118)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (22119)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (22120)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (22119)Refutation not found, incomplete strategy% (22119)------------------------------
% 0.22/0.47  % (22119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (22119)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (22119)Memory used [KB]: 10618
% 0.22/0.47  % (22119)Time elapsed: 0.060 s
% 0.22/0.47  % (22119)------------------------------
% 0.22/0.47  % (22119)------------------------------
% 0.22/0.47  % (22111)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (22110)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (22123)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (22112)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (22115)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (22125)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (22113)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (22111)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f485,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f478])).
% 0.22/0.49  fof(f478,plain,(
% 0.22/0.49    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 0.22/0.49    inference(superposition,[],[f15,f468])).
% 0.22/0.49  fof(f468,plain,(
% 0.22/0.49    ( ! [X26,X24,X23,X21,X25,X22,X20] : (k5_enumset1(X25,X26,X20,X21,X22,X23,X24) = k2_xboole_0(k4_enumset1(X25,X26,X20,X21,X22,X23),k1_tarski(X24))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f458,f182])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    ( ! [X26,X24,X23,X21,X25,X22,X20] : (k2_xboole_0(k2_tarski(X25,X26),k3_enumset1(X20,X21,X22,X23,X24)) = k5_enumset1(X25,X26,X20,X21,X22,X23,X24)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f180,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_enumset1)).
% 0.22/0.49  fof(f180,plain,(
% 0.22/0.49    ( ! [X26,X24,X23,X21,X25,X22,X20] : (k2_xboole_0(k2_enumset1(X25,X26,X20,X21),k1_enumset1(X22,X23,X24)) = k2_xboole_0(k2_tarski(X25,X26),k3_enumset1(X20,X21,X22,X23,X24))) )),
% 0.22/0.49    inference(superposition,[],[f81,f148])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    ( ! [X14,X17,X15,X18,X16] : (k2_xboole_0(k2_tarski(X17,X18),k1_enumset1(X14,X15,X16)) = k3_enumset1(X17,X18,X14,X15,X16)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f141,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    ( ! [X14,X17,X15,X18,X16] : (k2_xboole_0(k2_enumset1(X17,X18,X14,X15),k1_tarski(X16)) = k2_xboole_0(k2_tarski(X17,X18),k1_enumset1(X14,X15,X16))) )),
% 0.22/0.49    inference(superposition,[],[f81,f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    ( ! [X14,X17,X15,X18,X16] : (k2_xboole_0(k2_tarski(X16,X17),k2_xboole_0(k2_tarski(X14,X15),X18)) = k2_xboole_0(k2_enumset1(X16,X17,X14,X15),X18)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f72,f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ( ! [X14,X17,X15,X18,X16] : (k2_xboole_0(k2_xboole_0(k1_enumset1(X16,X17,X14),k1_tarski(X15)),X18) = k2_xboole_0(k2_tarski(X16,X17),k2_xboole_0(k2_tarski(X14,X15),X18))) )),
% 0.22/0.49    inference(superposition,[],[f27,f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X6,X4,X8,X7,X5] : (k2_xboole_0(k2_tarski(X4,X5),k2_xboole_0(k2_xboole_0(k1_tarski(X6),X7),X8)) = k2_xboole_0(k2_xboole_0(k1_enumset1(X4,X5,X6),X7),X8)) )),
% 0.22/0.49    inference(superposition,[],[f20,f18])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_xboole_1)).
% 0.22/0.49  fof(f458,plain,(
% 0.22/0.49    ( ! [X26,X24,X23,X21,X25,X22,X20] : (k2_xboole_0(k2_tarski(X25,X26),k3_enumset1(X20,X21,X22,X23,X24)) = k2_xboole_0(k4_enumset1(X25,X26,X20,X21,X22,X23),k1_tarski(X24))) )),
% 0.22/0.49    inference(superposition,[],[f200,f21])).
% 0.22/0.49  fof(f200,plain,(
% 0.22/0.49    ( ! [X24,X23,X21,X19,X22,X20,X18] : (k2_xboole_0(k2_tarski(X20,X21),k2_xboole_0(k2_enumset1(X22,X23,X18,X19),X24)) = k2_xboole_0(k4_enumset1(X20,X21,X22,X23,X18,X19),X24)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f199,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).
% 0.22/0.49  fof(f199,plain,(
% 0.22/0.49    ( ! [X24,X23,X21,X19,X22,X20,X18] : (k2_xboole_0(k2_xboole_0(k3_enumset1(X20,X21,X22,X23,X18),k1_tarski(X19)),X24) = k2_xboole_0(k2_tarski(X20,X21),k2_xboole_0(k2_enumset1(X22,X23,X18,X19),X24))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f186,f140])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k2_xboole_0(k2_enumset1(X12,X13,X7,X8),k2_xboole_0(k2_tarski(X9,X10),X11)) = k2_xboole_0(k2_tarski(X12,X13),k2_xboole_0(k2_enumset1(X7,X8,X9,X10),X11))) )),
% 0.22/0.49    inference(superposition,[],[f81,f81])).
% 0.22/0.49  fof(f186,plain,(
% 0.22/0.49    ( ! [X24,X23,X21,X19,X22,X20,X18] : (k2_xboole_0(k2_xboole_0(k3_enumset1(X20,X21,X22,X23,X18),k1_tarski(X19)),X24) = k2_xboole_0(k2_enumset1(X20,X21,X22,X23),k2_xboole_0(k2_tarski(X18,X19),X24))) )),
% 0.22/0.49    inference(superposition,[],[f33,f16])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k2_xboole_0(k1_tarski(X4),X5),X6)) = k2_xboole_0(k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5),X6)) )),
% 0.22/0.49    inference(superposition,[],[f20,f21])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f12,f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 0.22/0.49    inference(negated_conjecture,[],[f10])).
% 0.22/0.49  fof(f10,conjecture,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (22111)------------------------------
% 0.22/0.49  % (22111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22111)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (22111)Memory used [KB]: 2430
% 0.22/0.49  % (22111)Time elapsed: 0.081 s
% 0.22/0.49  % (22111)------------------------------
% 0.22/0.49  % (22111)------------------------------
% 0.22/0.50  % (22103)Success in time 0.139 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 355 expanded)
%              Number of leaves         :   12 ( 122 expanded)
%              Depth                    :   18
%              Number of atoms          :   64 ( 356 expanded)
%              Number of equality atoms :   63 ( 355 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3204,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f3203])).

fof(f3203,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f3189,f34])).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f21,f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f3189,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f3188,f1558])).

fof(f1558,plain,(
    ! [X10,X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X10,k2_xboole_0(X8,X9))) ),
    inference(superposition,[],[f220,f21])).

fof(f220,plain,(
    ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(k2_xboole_0(X4,X5),X6)) ),
    inference(forward_demodulation,[],[f214,f140])).

fof(f140,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5) ),
    inference(backward_demodulation,[],[f44,f139])).

fof(f139,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f111,f53])).

fof(f53,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)) ),
    inference(superposition,[],[f31,f34])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f111,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f30,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f23,f23])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f44,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(X5,X5) ),
    inference(superposition,[],[f25,f34])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f214,plain,(
    ! [X6,X4,X5] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X4,k2_xboole_0(k2_xboole_0(X4,X5),X6)) ),
    inference(superposition,[],[f28,f155])).

fof(f155,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f150,f140])).

fof(f150,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(backward_demodulation,[],[f56,f140])).

fof(f56,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3) ),
    inference(superposition,[],[f28,f44])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f3188,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f3185,f28])).

fof(f3185,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f393,f3121])).

fof(f3121,plain,(
    ! [X61,X62,X63] : k4_xboole_0(k2_xboole_0(X63,k4_xboole_0(X61,X62)),k2_xboole_0(X62,X61)) = k4_xboole_0(X63,k2_xboole_0(X62,X61)) ),
    inference(superposition,[],[f66,f671])).

fof(f671,plain,(
    ! [X12,X13] : k2_xboole_0(X12,X13) = k2_xboole_0(k4_xboole_0(X13,X12),X12) ),
    inference(forward_demodulation,[],[f636,f42])).

fof(f42,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f25,f21])).

fof(f636,plain,(
    ! [X12,X13] : k2_xboole_0(X12,X13) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X12,X13),X12),X12) ),
    inference(superposition,[],[f33,f161])).

fof(f161,plain,(
    ! [X8,X9] : k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8)) = X8 ),
    inference(forward_demodulation,[],[f160,f19])).

fof(f160,plain,(
    ! [X8,X9] : k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8)) = k4_xboole_0(X8,k1_xboole_0) ),
    inference(forward_demodulation,[],[f113,f155])).

fof(f113,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))) = k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8)) ),
    inference(superposition,[],[f30,f42])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f26,f23])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f66,plain,(
    ! [X6,X4,X5] : k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(X4,k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f57,f28])).

fof(f57,plain,(
    ! [X6,X4,X5] : k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(k4_xboole_0(X4,X5),X6) ),
    inference(superposition,[],[f28,f25])).

fof(f393,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f392,f30])).

fof(f392,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) ),
    inference(backward_demodulation,[],[f29,f372])).

fof(f372,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[],[f28,f218])).

fof(f218,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7 ),
    inference(forward_demodulation,[],[f217,f19])).

fof(f217,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = k4_xboole_0(X7,k1_xboole_0) ),
    inference(backward_demodulation,[],[f112,f208])).

fof(f208,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f155,f21])).

fof(f112,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X6,X7))) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f30,f25])).

fof(f29,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f17,f23,f27,f27])).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

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
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:21:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.40  % (9185)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (9172)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (9187)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (9176)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (9179)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (9173)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (9184)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (9177)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (9182)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (9181)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (9186)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (9189)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (9180)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (9183)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (9178)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (9183)Refutation not found, incomplete strategy% (9183)------------------------------
% 0.20/0.49  % (9183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (9175)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (9183)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (9183)Memory used [KB]: 10490
% 0.20/0.50  % (9183)Time elapsed: 0.085 s
% 0.20/0.50  % (9183)------------------------------
% 0.20/0.50  % (9183)------------------------------
% 0.20/0.50  % (9188)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (9174)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.58  % (9173)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f3204,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(trivial_inequality_removal,[],[f3203])).
% 0.20/0.58  fof(f3203,plain,(
% 0.20/0.58    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.58    inference(superposition,[],[f3189,f34])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.58    inference(superposition,[],[f21,f18])).
% 0.20/0.58  fof(f18,plain,(
% 0.20/0.58    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f4])).
% 0.20/0.58  fof(f4,axiom,(
% 0.20/0.58    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.58  fof(f21,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.58  fof(f3189,plain,(
% 0.20/0.58    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.58    inference(forward_demodulation,[],[f3188,f1558])).
% 0.20/0.58  fof(f1558,plain,(
% 0.20/0.58    ( ! [X10,X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X10,k2_xboole_0(X8,X9)))) )),
% 0.20/0.58    inference(superposition,[],[f220,f21])).
% 0.20/0.58  fof(f220,plain,(
% 0.20/0.58    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(k2_xboole_0(X4,X5),X6))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f214,f140])).
% 0.20/0.58  fof(f140,plain,(
% 0.20/0.58    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)) )),
% 0.20/0.58    inference(backward_demodulation,[],[f44,f139])).
% 0.20/0.58  fof(f139,plain,(
% 0.20/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.58    inference(forward_demodulation,[],[f111,f53])).
% 0.20/0.58  fof(f53,plain,(
% 0.20/0.58    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6))) )),
% 0.20/0.58    inference(superposition,[],[f31,f34])).
% 0.20/0.58  fof(f31,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 0.20/0.58    inference(definition_unfolding,[],[f22,f23])).
% 0.20/0.58  fof(f23,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,axiom,(
% 0.20/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.58  fof(f22,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f5])).
% 0.20/0.58  fof(f5,axiom,(
% 0.20/0.58    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.20/0.58  fof(f111,plain,(
% 0.20/0.58    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 0.20/0.58    inference(superposition,[],[f30,f19])).
% 0.20/0.58  fof(f19,plain,(
% 0.20/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f6])).
% 0.20/0.58  fof(f6,axiom,(
% 0.20/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.58  fof(f30,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f20,f23,f23])).
% 0.20/0.58  fof(f20,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.58  fof(f44,plain,(
% 0.20/0.58    ( ! [X5] : (k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(X5,X5)) )),
% 0.20/0.58    inference(superposition,[],[f25,f34])).
% 0.20/0.58  fof(f25,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f7])).
% 0.20/0.58  fof(f7,axiom,(
% 0.20/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.20/0.58  fof(f214,plain,(
% 0.20/0.58    ( ! [X6,X4,X5] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X4,k2_xboole_0(k2_xboole_0(X4,X5),X6))) )),
% 0.20/0.58    inference(superposition,[],[f28,f155])).
% 0.20/0.58  fof(f155,plain,(
% 0.20/0.58    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f150,f140])).
% 0.20/0.58  fof(f150,plain,(
% 0.20/0.58    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 0.20/0.58    inference(backward_demodulation,[],[f56,f140])).
% 0.20/0.58  fof(f56,plain,(
% 0.20/0.58    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3)) )),
% 0.20/0.58    inference(superposition,[],[f28,f44])).
% 0.20/0.58  fof(f28,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f8])).
% 0.20/0.58  fof(f8,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.58  fof(f3188,plain,(
% 0.20/0.58    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.58    inference(forward_demodulation,[],[f3185,f28])).
% 0.20/0.58  fof(f3185,plain,(
% 0.20/0.58    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.58    inference(backward_demodulation,[],[f393,f3121])).
% 0.20/0.58  fof(f3121,plain,(
% 0.20/0.58    ( ! [X61,X62,X63] : (k4_xboole_0(k2_xboole_0(X63,k4_xboole_0(X61,X62)),k2_xboole_0(X62,X61)) = k4_xboole_0(X63,k2_xboole_0(X62,X61))) )),
% 0.20/0.58    inference(superposition,[],[f66,f671])).
% 0.20/0.58  fof(f671,plain,(
% 0.20/0.58    ( ! [X12,X13] : (k2_xboole_0(X12,X13) = k2_xboole_0(k4_xboole_0(X13,X12),X12)) )),
% 0.20/0.58    inference(forward_demodulation,[],[f636,f42])).
% 0.20/0.58  fof(f42,plain,(
% 0.20/0.58    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 0.20/0.58    inference(superposition,[],[f25,f21])).
% 0.20/0.58  fof(f636,plain,(
% 0.20/0.58    ( ! [X12,X13] : (k2_xboole_0(X12,X13) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X12,X13),X12),X12)) )),
% 0.20/0.58    inference(superposition,[],[f33,f161])).
% 0.20/0.58  fof(f161,plain,(
% 0.20/0.58    ( ! [X8,X9] : (k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8)) = X8) )),
% 0.20/0.58    inference(forward_demodulation,[],[f160,f19])).
% 0.20/0.58  fof(f160,plain,(
% 0.20/0.58    ( ! [X8,X9] : (k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8)) = k4_xboole_0(X8,k1_xboole_0)) )),
% 0.20/0.58    inference(forward_demodulation,[],[f113,f155])).
% 0.20/0.58  fof(f113,plain,(
% 0.20/0.58    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))) = k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8))) )),
% 0.20/0.58    inference(superposition,[],[f30,f42])).
% 0.20/0.58  fof(f33,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.58    inference(definition_unfolding,[],[f26,f23])).
% 0.20/0.58  fof(f26,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f11])).
% 0.20/0.58  fof(f11,axiom,(
% 0.20/0.58    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.20/0.58  fof(f66,plain,(
% 0.20/0.58    ( ! [X6,X4,X5] : (k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(X4,k2_xboole_0(X5,X6))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f57,f28])).
% 0.20/0.58  fof(f57,plain,(
% 0.20/0.58    ( ! [X6,X4,X5] : (k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(k4_xboole_0(X4,X5),X6)) )),
% 0.20/0.58    inference(superposition,[],[f28,f25])).
% 0.20/0.58  fof(f393,plain,(
% 0.20/0.58    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.58    inference(forward_demodulation,[],[f392,f30])).
% 0.20/0.58  fof(f392,plain,(
% 0.20/0.58    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))),
% 0.20/0.58    inference(backward_demodulation,[],[f29,f372])).
% 0.20/0.58  fof(f372,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 0.20/0.58    inference(superposition,[],[f28,f218])).
% 0.20/0.58  fof(f218,plain,(
% 0.20/0.58    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7) )),
% 0.20/0.58    inference(forward_demodulation,[],[f217,f19])).
% 0.20/0.58  fof(f217,plain,(
% 0.20/0.58    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = k4_xboole_0(X7,k1_xboole_0)) )),
% 0.20/0.58    inference(backward_demodulation,[],[f112,f208])).
% 0.20/0.58  fof(f208,plain,(
% 0.20/0.58    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 0.20/0.58    inference(superposition,[],[f155,f21])).
% 0.20/0.58  fof(f112,plain,(
% 0.20/0.58    ( ! [X6,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X6,X7))) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7))) )),
% 0.20/0.58    inference(superposition,[],[f30,f25])).
% 0.20/0.58  fof(f29,plain,(
% 0.20/0.58    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.20/0.58    inference(definition_unfolding,[],[f17,f23,f27,f27])).
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f3])).
% 0.20/0.58  fof(f3,axiom,(
% 0.20/0.58    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.20/0.58  fof(f17,plain,(
% 0.20/0.58    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.20/0.58    inference(cnf_transformation,[],[f16])).
% 0.20/0.58  fof(f16,plain,(
% 0.20/0.58    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 0.20/0.58  fof(f15,plain,(
% 0.20/0.58    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f14,plain,(
% 0.20/0.58    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f13])).
% 0.20/0.58  fof(f13,negated_conjecture,(
% 0.20/0.58    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.20/0.58    inference(negated_conjecture,[],[f12])).
% 0.20/0.58  fof(f12,conjecture,(
% 0.20/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (9173)------------------------------
% 0.20/0.58  % (9173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (9173)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (9173)Memory used [KB]: 3326
% 0.20/0.58  % (9173)Time elapsed: 0.143 s
% 0.20/0.58  % (9173)------------------------------
% 0.20/0.58  % (9173)------------------------------
% 0.20/0.58  % (9171)Success in time 0.23 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 412 expanded)
%              Number of leaves         :   11 ( 139 expanded)
%              Depth                    :   23
%              Number of atoms          :   67 ( 413 expanded)
%              Number of equality atoms :   66 ( 412 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1908,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1907])).

fof(f1907,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f34,f1726])).

fof(f1726,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(forward_demodulation,[],[f1725,f16])).

fof(f16,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f1725,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1685,f495])).

fof(f495,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(superposition,[],[f416,f17])).

fof(f17,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f416,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[],[f394,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(forward_demodulation,[],[f27,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f18,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f394,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
    inference(forward_demodulation,[],[f30,f23])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1685,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0)) ),
    inference(backward_demodulation,[],[f554,f1649])).

fof(f1649,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k4_xboole_0(X6,X7)) = X7 ),
    inference(superposition,[],[f751,f1591])).

fof(f1591,plain,(
    ! [X17,X18,X16] : k4_xboole_0(X16,X17) = k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X17,X18)) ),
    inference(forward_demodulation,[],[f1546,f17])).

fof(f1546,plain,(
    ! [X17,X18,X16] : k4_xboole_0(k4_xboole_0(X16,X17),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X17,X18)) ),
    inference(superposition,[],[f566,f1052])).

fof(f1052,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X4))) ),
    inference(forward_demodulation,[],[f1051,f491])).

fof(f491,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f416,f17])).

fof(f1051,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X4))) ),
    inference(forward_demodulation,[],[f1041,f495])).

fof(f1041,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X4))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)),X4) ),
    inference(superposition,[],[f29,f1007])).

fof(f1007,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(backward_demodulation,[],[f569,f945])).

fof(f945,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f944,f16])).

fof(f944,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f943,f16])).

fof(f943,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f942,f495])).

fof(f942,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f919,f17])).

fof(f919,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[],[f554,f495])).

fof(f569,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X0,X0))) ),
    inference(forward_demodulation,[],[f561,f17])).

fof(f561,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)))) ),
    inference(superposition,[],[f394,f495])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f22,f20,f20])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f566,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X8) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X7,X8))) ),
    inference(forward_demodulation,[],[f556,f16])).

fof(f556,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X8) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(k5_xboole_0(X7,k1_xboole_0),X8))) ),
    inference(backward_demodulation,[],[f103,f495])).

fof(f103,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X7,X7)),X8))) = k4_xboole_0(X7,X8) ),
    inference(forward_demodulation,[],[f86,f17])).

fof(f86,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X7,X7)),X8))) = k4_xboole_0(k4_xboole_0(X7,k1_xboole_0),X8) ),
    inference(superposition,[],[f29,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X0))) ),
    inference(forward_demodulation,[],[f46,f31])).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f23,f16])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)))) ),
    inference(superposition,[],[f45,f17])).

fof(f751,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = X1 ),
    inference(forward_demodulation,[],[f708,f17])).

fof(f708,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(superposition,[],[f566,f560])).

fof(f560,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X4))))) ),
    inference(superposition,[],[f495,f29])).

fof(f554,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(forward_demodulation,[],[f28,f23])).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f19,f25,f25])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f34,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f26,f23])).

fof(f26,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f15,f25])).

fof(f15,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:39:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (25058)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.43  % (25067)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (25069)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (25059)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (25062)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (25061)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (25060)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (25071)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (25070)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (25068)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (25068)Refutation not found, incomplete strategy% (25068)------------------------------
% 0.22/0.49  % (25068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (25068)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (25068)Memory used [KB]: 10490
% 0.22/0.49  % (25068)Time elapsed: 0.061 s
% 0.22/0.49  % (25068)------------------------------
% 0.22/0.49  % (25068)------------------------------
% 0.22/0.49  % (25056)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.50  % (25073)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (25063)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (25074)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (25072)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (25064)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.52  % (25069)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f1908,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f1907])).
% 0.22/0.52  fof(f1907,plain,(
% 0.22/0.52    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.52    inference(superposition,[],[f34,f1726])).
% 0.22/0.52  fof(f1726,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f1725,f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.52  fof(f1725,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f1685,f495])).
% 0.22/0.52  fof(f495,plain,(
% 0.22/0.52    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 0.22/0.52    inference(superposition,[],[f416,f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.52  fof(f416,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 0.22/0.52    inference(superposition,[],[f394,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f27,f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f18,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f21,f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.22/0.52  fof(f394,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f30,f23])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f24,f25])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.52  fof(f1685,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0))) )),
% 0.22/0.52    inference(backward_demodulation,[],[f554,f1649])).
% 0.22/0.52  fof(f1649,plain,(
% 0.22/0.52    ( ! [X6,X7] : (k4_xboole_0(X7,k4_xboole_0(X6,X7)) = X7) )),
% 0.22/0.52    inference(superposition,[],[f751,f1591])).
% 0.22/0.52  fof(f1591,plain,(
% 0.22/0.52    ( ! [X17,X18,X16] : (k4_xboole_0(X16,X17) = k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X17,X18))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f1546,f17])).
% 0.22/0.52  fof(f1546,plain,(
% 0.22/0.52    ( ! [X17,X18,X16] : (k4_xboole_0(k4_xboole_0(X16,X17),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X17,X18))) )),
% 0.22/0.52    inference(superposition,[],[f566,f1052])).
% 0.22/0.52  fof(f1052,plain,(
% 0.22/0.52    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X4)))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f1051,f491])).
% 0.22/0.52  fof(f491,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(superposition,[],[f416,f17])).
% 0.22/0.52  fof(f1051,plain,(
% 0.22/0.52    ( ! [X4,X2,X3] : (k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X4)))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f1041,f495])).
% 0.22/0.52  fof(f1041,plain,(
% 0.22/0.52    ( ! [X4,X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X4))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)),X4)) )),
% 0.22/0.52    inference(superposition,[],[f29,f1007])).
% 0.22/0.52  fof(f1007,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 0.22/0.52    inference(backward_demodulation,[],[f569,f945])).
% 0.22/0.52  fof(f945,plain,(
% 0.22/0.52    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 0.22/0.52    inference(forward_demodulation,[],[f944,f16])).
% 0.22/0.52  fof(f944,plain,(
% 0.22/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(X0,X0))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f943,f16])).
% 0.22/0.52  fof(f943,plain,(
% 0.22/0.52    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f942,f495])).
% 0.22/0.52  fof(f942,plain,(
% 0.22/0.52    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f919,f17])).
% 0.22/0.52  fof(f919,plain,(
% 0.22/0.52    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)))) )),
% 0.22/0.52    inference(superposition,[],[f554,f495])).
% 0.22/0.52  fof(f569,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X0,X0)))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f561,f17])).
% 0.22/0.52  fof(f561,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))))) )),
% 0.22/0.52    inference(superposition,[],[f394,f495])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f22,f20,f20])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.52  fof(f566,plain,(
% 0.22/0.52    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X7,X8)))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f556,f16])).
% 0.22/0.52  fof(f556,plain,(
% 0.22/0.52    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(k5_xboole_0(X7,k1_xboole_0),X8)))) )),
% 0.22/0.52    inference(backward_demodulation,[],[f103,f495])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X7,X7)),X8))) = k4_xboole_0(X7,X8)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f86,f17])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X7,X7)),X8))) = k4_xboole_0(k4_xboole_0(X7,k1_xboole_0),X8)) )),
% 0.22/0.52    inference(superposition,[],[f29,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X0)))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f46,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) )),
% 0.22/0.52    inference(superposition,[],[f23,f16])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))))) )),
% 0.22/0.52    inference(superposition,[],[f45,f17])).
% 0.22/0.52  fof(f751,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = X1) )),
% 0.22/0.52    inference(forward_demodulation,[],[f708,f17])).
% 0.22/0.52  fof(f708,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k4_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 0.22/0.52    inference(superposition,[],[f566,f560])).
% 0.22/0.52  fof(f560,plain,(
% 0.22/0.52    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X4)))))) )),
% 0.22/0.52    inference(superposition,[],[f495,f29])).
% 0.22/0.52  fof(f554,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f28,f23])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f19,f25,f25])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 0.22/0.52    inference(superposition,[],[f26,f23])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.22/0.52    inference(definition_unfolding,[],[f15,f25])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.52    inference(negated_conjecture,[],[f10])).
% 0.22/0.52  fof(f10,conjecture,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (25069)------------------------------
% 0.22/0.52  % (25069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25069)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (25069)Memory used [KB]: 2686
% 0.22/0.52  % (25069)Time elapsed: 0.086 s
% 0.22/0.52  % (25069)------------------------------
% 0.22/0.52  % (25069)------------------------------
% 0.22/0.52  % (25055)Success in time 0.161 s
%------------------------------------------------------------------------------

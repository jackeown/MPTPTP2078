%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 (1135 expanded)
%              Number of leaves         :   13 ( 397 expanded)
%              Depth                    :   26
%              Number of atoms          :   77 (1136 expanded)
%              Number of equality atoms :   76 (1135 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3601,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f3600])).

fof(f3600,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f30,f3433])).

fof(f3433,plain,(
    ! [X12,X11] : k4_xboole_0(X11,X12) = k5_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f3432,f45])).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f39,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f18,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f32,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f20,f22,f22])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f3432,plain,(
    ! [X12,X11] : k5_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X11,X12)) ),
    inference(forward_demodulation,[],[f3431,f1195])).

fof(f1195,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f61,f1189])).

fof(f1189,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(forward_demodulation,[],[f1171,f174])).

fof(f174,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f168,f61])).

fof(f168,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f150,f45])).

fof(f150,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X0) ),
    inference(superposition,[],[f35,f19])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(definition_unfolding,[],[f25,f22])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1171,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(superposition,[],[f1088,f503])).

fof(f503,plain,(
    ! [X14] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X14)) = k5_xboole_0(X14,X14) ),
    inference(forward_demodulation,[],[f488,f307])).

fof(f307,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X6,X6)) ),
    inference(backward_demodulation,[],[f92,f260])).

fof(f260,plain,(
    ! [X6] : k4_xboole_0(X6,X6) = k5_xboole_0(X6,X6) ),
    inference(superposition,[],[f29,f177])).

fof(f177,plain,(
    ! [X2] : k5_xboole_0(X2,k4_xboole_0(X2,X2)) = X2 ),
    inference(superposition,[],[f31,f168])).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f22])).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f92,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X6)) ),
    inference(superposition,[],[f34,f61])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f488,plain,(
    ! [X14] : k5_xboole_0(X14,X14) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X14,X14))) ),
    inference(superposition,[],[f34,f448])).

fof(f448,plain,(
    ! [X1] : k5_xboole_0(X1,X1) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f176,f260])).

fof(f176,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)) ),
    inference(superposition,[],[f61,f168])).

fof(f1088,plain,(
    ! [X11] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X11),k4_xboole_0(k1_xboole_0,X11)) ),
    inference(forward_demodulation,[],[f1087,f34])).

fof(f1087,plain,(
    ! [X11] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X11),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X11)))) ),
    inference(forward_demodulation,[],[f1026,f61])).

fof(f1026,plain,(
    ! [X11] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X11),k4_xboole_0(k4_xboole_0(k1_xboole_0,X11),k4_xboole_0(k1_xboole_0,X11))) ),
    inference(superposition,[],[f36,f174])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f26,f22,f23])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f61,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f33,f19])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f21,f23,f23])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f3431,plain,(
    ! [X12,X11] : k5_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12))) = k5_xboole_0(k4_xboole_0(X11,X11),k4_xboole_0(X11,X12)) ),
    inference(forward_demodulation,[],[f3430,f1410])).

fof(f1410,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X9,X8)) = X8 ),
    inference(forward_demodulation,[],[f1387,f19])).

fof(f1387,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k1_xboole_0) = k4_xboole_0(X8,k4_xboole_0(X9,X8)) ),
    inference(superposition,[],[f34,f1285])).

fof(f1285,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(forward_demodulation,[],[f1265,f90])).

fof(f90,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f34,f33])).

fof(f1265,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
    inference(superposition,[],[f1195,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f28,f23,f23])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f3430,plain,(
    ! [X12,X11] : k5_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12))) = k5_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X11))),k4_xboole_0(X11,X12)) ),
    inference(forward_demodulation,[],[f3429,f37])).

fof(f3429,plain,(
    ! [X12,X11] : k5_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11),k4_xboole_0(X11,X12)) ),
    inference(forward_demodulation,[],[f3353,f2026])).

fof(f2026,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X6,k4_xboole_0(k4_xboole_0(X7,X6),X8)) = X6 ),
    inference(forward_demodulation,[],[f1974,f19])).

fof(f1974,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X6,k1_xboole_0) = k4_xboole_0(X6,k4_xboole_0(k4_xboole_0(X7,X6),X8)) ),
    inference(superposition,[],[f34,f1409])).

fof(f1409,plain,(
    ! [X6,X7,X5] : k1_xboole_0 = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X6,X5),X7))) ),
    inference(forward_demodulation,[],[f1386,f1264])).

fof(f1264,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f168,f1195])).

fof(f1386,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k1_xboole_0,X7) = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X6,X5),X7))) ),
    inference(superposition,[],[f37,f1285])).

fof(f3353,plain,(
    ! [X12,X11] : k5_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11),k4_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11))) ),
    inference(superposition,[],[f258,f34])).

fof(f258,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) = k5_xboole_0(X2,X3) ),
    inference(superposition,[],[f29,f32])).

fof(f30,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f17,f23])).

fof(f17,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:16:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (25964)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (25957)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (25953)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (25952)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (25956)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (25966)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (25964)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f3601,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f3600])).
% 0.21/0.47  fof(f3600,plain,(
% 0.21/0.47    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)),
% 0.21/0.47    inference(superposition,[],[f30,f3433])).
% 0.21/0.47  fof(f3433,plain,(
% 0.21/0.47    ( ! [X12,X11] : (k4_xboole_0(X11,X12) = k5_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12)))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f3432,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.47    inference(forward_demodulation,[],[f39,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 0.21/0.47    inference(definition_unfolding,[],[f18,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(superposition,[],[f32,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f20,f22,f22])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.47  fof(f3432,plain,(
% 0.21/0.47    ( ! [X12,X11] : (k5_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X11,X12))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f3431,f1195])).
% 0.21/0.47  fof(f1195,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.47    inference(backward_demodulation,[],[f61,f1189])).
% 0.21/0.47  fof(f1189,plain,(
% 0.21/0.47    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f1171,f174])).
% 0.21/0.47  fof(f174,plain,(
% 0.21/0.47    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) )),
% 0.21/0.47    inference(superposition,[],[f168,f61])).
% 0.21/0.47  fof(f168,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f150,f45])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X0)) )),
% 0.21/0.47    inference(superposition,[],[f35,f19])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f25,f22])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.47  fof(f1171,plain,(
% 0.21/0.47    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))) )),
% 0.21/0.47    inference(superposition,[],[f1088,f503])).
% 0.21/0.47  fof(f503,plain,(
% 0.21/0.47    ( ! [X14] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X14)) = k5_xboole_0(X14,X14)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f488,f307])).
% 0.21/0.47  fof(f307,plain,(
% 0.21/0.47    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X6,X6))) )),
% 0.21/0.47    inference(backward_demodulation,[],[f92,f260])).
% 0.21/0.47  fof(f260,plain,(
% 0.21/0.47    ( ! [X6] : (k4_xboole_0(X6,X6) = k5_xboole_0(X6,X6)) )),
% 0.21/0.47    inference(superposition,[],[f29,f177])).
% 0.21/0.47  fof(f177,plain,(
% 0.21/0.47    ( ! [X2] : (k5_xboole_0(X2,k4_xboole_0(X2,X2)) = X2) )),
% 0.21/0.47    inference(superposition,[],[f31,f168])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f27,f22])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X6))) )),
% 0.21/0.47    inference(superposition,[],[f34,f61])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f24,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.47  fof(f488,plain,(
% 0.21/0.47    ( ! [X14] : (k5_xboole_0(X14,X14) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X14,X14)))) )),
% 0.21/0.47    inference(superposition,[],[f34,f448])).
% 0.21/0.47  fof(f448,plain,(
% 0.21/0.47    ( ! [X1] : (k5_xboole_0(X1,X1) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f176,f260])).
% 0.21/0.47  fof(f176,plain,(
% 0.21/0.47    ( ! [X1] : (k4_xboole_0(X1,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))) )),
% 0.21/0.47    inference(superposition,[],[f61,f168])).
% 0.21/0.47  fof(f1088,plain,(
% 0.21/0.47    ( ! [X11] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X11),k4_xboole_0(k1_xboole_0,X11))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f1087,f34])).
% 0.21/0.47  fof(f1087,plain,(
% 0.21/0.47    ( ! [X11] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X11),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X11))))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f1026,f61])).
% 0.21/0.47  fof(f1026,plain,(
% 0.21/0.47    ( ! [X11] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X11),k4_xboole_0(k4_xboole_0(k1_xboole_0,X11),k4_xboole_0(k1_xboole_0,X11)))) )),
% 0.21/0.47    inference(superposition,[],[f36,f174])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0) )),
% 0.21/0.47    inference(definition_unfolding,[],[f26,f22,f23])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0)) )),
% 0.21/0.47    inference(superposition,[],[f33,f19])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f21,f23,f23])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.47  fof(f3431,plain,(
% 0.21/0.47    ( ! [X12,X11] : (k5_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12))) = k5_xboole_0(k4_xboole_0(X11,X11),k4_xboole_0(X11,X12))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f3430,f1410])).
% 0.21/0.47  fof(f1410,plain,(
% 0.21/0.47    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X9,X8)) = X8) )),
% 0.21/0.47    inference(forward_demodulation,[],[f1387,f19])).
% 0.21/0.47  fof(f1387,plain,(
% 0.21/0.47    ( ! [X8,X9] : (k4_xboole_0(X8,k1_xboole_0) = k4_xboole_0(X8,k4_xboole_0(X9,X8))) )),
% 0.21/0.47    inference(superposition,[],[f34,f1285])).
% 0.21/0.47  fof(f1285,plain,(
% 0.21/0.47    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f1265,f90])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.21/0.47    inference(superposition,[],[f34,f33])).
% 0.21/0.47  fof(f1265,plain,(
% 0.21/0.47    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) )),
% 0.21/0.47    inference(superposition,[],[f1195,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f28,f23,f23])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.47  fof(f3430,plain,(
% 0.21/0.47    ( ! [X12,X11] : (k5_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12))) = k5_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X11))),k4_xboole_0(X11,X12))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f3429,f37])).
% 0.21/0.47  fof(f3429,plain,(
% 0.21/0.47    ( ! [X12,X11] : (k5_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11),k4_xboole_0(X11,X12))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f3353,f2026])).
% 0.21/0.47  fof(f2026,plain,(
% 0.21/0.47    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k4_xboole_0(k4_xboole_0(X7,X6),X8)) = X6) )),
% 0.21/0.47    inference(forward_demodulation,[],[f1974,f19])).
% 0.21/0.47  fof(f1974,plain,(
% 0.21/0.47    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k1_xboole_0) = k4_xboole_0(X6,k4_xboole_0(k4_xboole_0(X7,X6),X8))) )),
% 0.21/0.47    inference(superposition,[],[f34,f1409])).
% 0.21/0.47  fof(f1409,plain,(
% 0.21/0.47    ( ! [X6,X7,X5] : (k1_xboole_0 = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X6,X5),X7)))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f1386,f1264])).
% 0.21/0.47  fof(f1264,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(backward_demodulation,[],[f168,f1195])).
% 0.21/0.47  fof(f1386,plain,(
% 0.21/0.47    ( ! [X6,X7,X5] : (k4_xboole_0(k1_xboole_0,X7) = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X6,X5),X7)))) )),
% 0.21/0.47    inference(superposition,[],[f37,f1285])).
% 0.21/0.47  fof(f3353,plain,(
% 0.21/0.47    ( ! [X12,X11] : (k5_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11),k4_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11)))) )),
% 0.21/0.47    inference(superposition,[],[f258,f34])).
% 0.21/0.47  fof(f258,plain,(
% 0.21/0.47    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) = k5_xboole_0(X2,X3)) )),
% 0.21/0.47    inference(superposition,[],[f29,f32])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.21/0.47    inference(definition_unfolding,[],[f17,f23])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f12])).
% 0.21/0.47  fof(f12,conjecture,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (25964)------------------------------
% 0.21/0.47  % (25964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (25964)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (25964)Memory used [KB]: 3198
% 0.21/0.47  % (25964)Time elapsed: 0.065 s
% 0.21/0.47  % (25964)------------------------------
% 0.21/0.47  % (25964)------------------------------
% 0.21/0.47  % (25958)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (25951)Success in time 0.118 s
%------------------------------------------------------------------------------

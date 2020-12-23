%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:19 EST 2020

% Result     : Theorem 54.17s
% Output     : Refutation 54.17s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 860 expanded)
%              Number of leaves         :   12 ( 279 expanded)
%              Depth                    :   29
%              Number of atoms          :   79 ( 861 expanded)
%              Number of equality atoms :   78 ( 860 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f152255,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19,f152254])).

fof(f152254,plain,(
    ! [X233,X232] : k5_xboole_0(X232,X233) = k4_xboole_0(k2_xboole_0(X232,X233),k3_xboole_0(X232,X233)) ),
    inference(forward_demodulation,[],[f152253,f44])).

fof(f44,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f43,f23])).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f43,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f41,f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f41,plain,(
    ! [X2] : k2_xboole_0(X2,X2) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f26,f32])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f22,f20])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f22,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f152253,plain,(
    ! [X233,X232] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X232,X233)) = k4_xboole_0(k2_xboole_0(X232,X233),k3_xboole_0(X232,X233)) ),
    inference(forward_demodulation,[],[f152252,f3882])).

fof(f3882,plain,(
    ! [X26,X27,X25] : k1_xboole_0 = k3_xboole_0(X25,k4_xboole_0(X27,k2_xboole_0(X25,X26))) ),
    inference(superposition,[],[f2305,f138])).

fof(f138,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f130,f95])).

fof(f95,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f86,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f86,plain,(
    ! [X1] : k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(superposition,[],[f70,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f70,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(forward_demodulation,[],[f66,f20])).

fof(f66,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f26,f60])).

fof(f60,plain,(
    ! [X6] : k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f27,f44])).

fof(f130,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k1_xboole_0) = k3_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f28,f22])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f2305,plain,(
    ! [X19,X17,X18] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X19,X17),k4_xboole_0(X18,X17)) ),
    inference(superposition,[],[f773,f759])).

fof(f759,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X8,X7)) = X7 ),
    inference(forward_demodulation,[],[f747,f43])).

fof(f747,plain,(
    ! [X8,X7] : k5_xboole_0(X7,k1_xboole_0) = k4_xboole_0(X7,k4_xboole_0(X8,X7)) ),
    inference(superposition,[],[f27,f685])).

fof(f685,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f30,f289])).

fof(f289,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f22,f271])).

fof(f271,plain,(
    ! [X4,X3] : k2_xboole_0(k3_xboole_0(X3,X4),X3) = X3 ),
    inference(superposition,[],[f266,f28])).

fof(f266,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(backward_demodulation,[],[f135,f247])).

fof(f247,plain,(
    ! [X6,X5] : k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,X6)) = X5 ),
    inference(superposition,[],[f228,f27])).

fof(f228,plain,(
    ! [X10,X9] : k5_xboole_0(k5_xboole_0(X9,X10),X10) = X9 ),
    inference(superposition,[],[f205,f201])).

fof(f201,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f178,f44])).

fof(f178,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f29,f144])).

fof(f144,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f141,f32])).

fof(f141,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f27,f137])).

fof(f137,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f129,f95])).

fof(f129,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f28,f32])).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f205,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f201,f23])).

fof(f135,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f26,f28])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f773,plain,(
    ! [X14,X15,X16] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X14,k4_xboole_0(X15,X16)),X16) ),
    inference(superposition,[],[f740,f30])).

fof(f740,plain,(
    ! [X19,X20] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X20,X19),X19) ),
    inference(superposition,[],[f685,f401])).

fof(f401,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) = X6 ),
    inference(forward_demodulation,[],[f400,f138])).

fof(f400,plain,(
    ! [X6,X7] : k3_xboole_0(X6,k2_xboole_0(X6,X7)) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) ),
    inference(forward_demodulation,[],[f391,f24])).

fof(f391,plain,(
    ! [X6,X7] : k3_xboole_0(k2_xboole_0(X6,X7),X6) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) ),
    inference(superposition,[],[f28,f219])).

fof(f219,plain,(
    ! [X6,X5] : k4_xboole_0(k2_xboole_0(X5,X6),X5) = k4_xboole_0(X6,X5) ),
    inference(backward_demodulation,[],[f172,f209])).

fof(f209,plain,(
    ! [X12,X11] : k4_xboole_0(X12,X11) = k5_xboole_0(X11,k2_xboole_0(X11,X12)) ),
    inference(superposition,[],[f201,f26])).

fof(f172,plain,(
    ! [X6,X5] : k4_xboole_0(k2_xboole_0(X5,X6),X5) = k5_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f165,f23])).

fof(f165,plain,(
    ! [X6,X5] : k4_xboole_0(k2_xboole_0(X5,X6),X5) = k5_xboole_0(k2_xboole_0(X5,X6),X5) ),
    inference(superposition,[],[f58,f138])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f27,f24])).

fof(f152252,plain,(
    ! [X233,X232] : k4_xboole_0(k2_xboole_0(X232,X233),k3_xboole_0(X232,X233)) = k5_xboole_0(k3_xboole_0(X232,k4_xboole_0(X233,k2_xboole_0(X232,X233))),k5_xboole_0(X232,X233)) ),
    inference(forward_demodulation,[],[f151889,f30])).

fof(f151889,plain,(
    ! [X233,X232] : k4_xboole_0(k2_xboole_0(X232,X233),k3_xboole_0(X232,X233)) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X232,X233),k2_xboole_0(X232,X233)),k5_xboole_0(X232,X233)) ),
    inference(superposition,[],[f106215,f23329])).

fof(f23329,plain,(
    ! [X10,X11] : k5_xboole_0(X11,X10) = k5_xboole_0(k2_xboole_0(X11,X10),k3_xboole_0(X11,X10)) ),
    inference(superposition,[],[f183,f248])).

fof(f248,plain,(
    ! [X8,X7] : k5_xboole_0(k4_xboole_0(X7,X8),k3_xboole_0(X8,X7)) = X7 ),
    inference(superposition,[],[f228,f58])).

fof(f183,plain,(
    ! [X14,X15,X16] : k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X15,X14),X16)) = k5_xboole_0(k2_xboole_0(X14,X15),X16) ),
    inference(superposition,[],[f29,f26])).

fof(f106215,plain,(
    ! [X21,X22] : k4_xboole_0(X21,X22) = k5_xboole_0(k4_xboole_0(X22,X21),k5_xboole_0(X21,X22)) ),
    inference(superposition,[],[f205,f13484])).

fof(f13484,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)) ),
    inference(superposition,[],[f181,f227])).

fof(f227,plain,(
    ! [X8,X7] : k5_xboole_0(k3_xboole_0(X8,X7),k4_xboole_0(X7,X8)) = X7 ),
    inference(superposition,[],[f205,f58])).

fof(f181,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = k5_xboole_0(k4_xboole_0(X8,X9),X10) ),
    inference(superposition,[],[f29,f27])).

fof(f19,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:15:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (24307)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.45  % (24298)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.45  % (24302)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (24295)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (24291)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (24304)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (24293)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (24297)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (24303)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (24290)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (24292)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (24294)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (24301)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (24296)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (24299)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (24306)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (24301)Refutation not found, incomplete strategy% (24301)------------------------------
% 0.20/0.50  % (24301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (24301)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (24301)Memory used [KB]: 10490
% 0.20/0.50  % (24301)Time elapsed: 0.095 s
% 0.20/0.50  % (24301)------------------------------
% 0.20/0.50  % (24301)------------------------------
% 0.20/0.50  % (24305)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.52  % (24300)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 4.88/1.02  % (24294)Time limit reached!
% 4.88/1.02  % (24294)------------------------------
% 4.88/1.02  % (24294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.88/1.02  % (24294)Termination reason: Time limit
% 4.88/1.02  
% 4.88/1.02  % (24294)Memory used [KB]: 15479
% 4.88/1.02  % (24294)Time elapsed: 0.614 s
% 4.88/1.02  % (24294)------------------------------
% 4.88/1.02  % (24294)------------------------------
% 12.52/1.97  % (24296)Time limit reached!
% 12.52/1.97  % (24296)------------------------------
% 12.52/1.97  % (24296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.52/1.97  % (24296)Termination reason: Time limit
% 12.52/1.97  
% 12.52/1.97  % (24296)Memory used [KB]: 42344
% 12.52/1.97  % (24296)Time elapsed: 1.521 s
% 12.52/1.97  % (24296)------------------------------
% 12.52/1.97  % (24296)------------------------------
% 12.84/2.03  % (24295)Time limit reached!
% 12.84/2.03  % (24295)------------------------------
% 12.84/2.03  % (24295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.84/2.03  % (24295)Termination reason: Time limit
% 12.84/2.03  
% 12.84/2.03  % (24295)Memory used [KB]: 45542
% 12.84/2.03  % (24295)Time elapsed: 1.625 s
% 12.84/2.03  % (24295)------------------------------
% 12.84/2.03  % (24295)------------------------------
% 14.39/2.22  % (24292)Time limit reached!
% 14.39/2.22  % (24292)------------------------------
% 14.39/2.22  % (24292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.39/2.23  % (24292)Termination reason: Time limit
% 14.39/2.23  
% 14.39/2.23  % (24292)Memory used [KB]: 41577
% 14.39/2.23  % (24292)Time elapsed: 1.812 s
% 14.39/2.23  % (24292)------------------------------
% 14.39/2.23  % (24292)------------------------------
% 18.35/2.68  % (24302)Time limit reached!
% 18.35/2.68  % (24302)------------------------------
% 18.35/2.68  % (24302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.35/2.68  % (24302)Termination reason: Time limit
% 18.35/2.68  % (24302)Termination phase: Saturation
% 18.35/2.68  
% 18.35/2.68  % (24302)Memory used [KB]: 64860
% 18.35/2.68  % (24302)Time elapsed: 2.200 s
% 18.35/2.68  % (24302)------------------------------
% 18.35/2.68  % (24302)------------------------------
% 54.17/7.22  % (24306)Refutation found. Thanks to Tanya!
% 54.17/7.22  % SZS status Theorem for theBenchmark
% 54.17/7.22  % SZS output start Proof for theBenchmark
% 54.17/7.22  fof(f152255,plain,(
% 54.17/7.22    $false),
% 54.17/7.22    inference(subsumption_resolution,[],[f19,f152254])).
% 54.17/7.22  fof(f152254,plain,(
% 54.17/7.22    ( ! [X233,X232] : (k5_xboole_0(X232,X233) = k4_xboole_0(k2_xboole_0(X232,X233),k3_xboole_0(X232,X233))) )),
% 54.17/7.22    inference(forward_demodulation,[],[f152253,f44])).
% 54.17/7.22  fof(f44,plain,(
% 54.17/7.22    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 54.17/7.22    inference(superposition,[],[f43,f23])).
% 54.17/7.22  fof(f23,plain,(
% 54.17/7.22    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 54.17/7.22    inference(cnf_transformation,[],[f2])).
% 54.17/7.22  fof(f2,axiom,(
% 54.17/7.22    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 54.17/7.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 54.17/7.22  fof(f43,plain,(
% 54.17/7.22    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = X2) )),
% 54.17/7.22    inference(forward_demodulation,[],[f41,f21])).
% 54.17/7.22  fof(f21,plain,(
% 54.17/7.22    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 54.17/7.22    inference(cnf_transformation,[],[f15])).
% 54.17/7.22  fof(f15,plain,(
% 54.17/7.22    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 54.17/7.22    inference(rectify,[],[f3])).
% 54.17/7.22  fof(f3,axiom,(
% 54.17/7.22    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 54.17/7.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 54.17/7.22  fof(f41,plain,(
% 54.17/7.22    ( ! [X2] : (k2_xboole_0(X2,X2) = k5_xboole_0(X2,k1_xboole_0)) )),
% 54.17/7.22    inference(superposition,[],[f26,f32])).
% 54.17/7.22  fof(f32,plain,(
% 54.17/7.22    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 54.17/7.22    inference(superposition,[],[f22,f20])).
% 54.17/7.22  fof(f20,plain,(
% 54.17/7.22    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 54.17/7.22    inference(cnf_transformation,[],[f6])).
% 54.17/7.22  fof(f6,axiom,(
% 54.17/7.22    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 54.17/7.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 54.17/7.22  fof(f22,plain,(
% 54.17/7.22    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 54.17/7.22    inference(cnf_transformation,[],[f8])).
% 54.17/7.22  fof(f8,axiom,(
% 54.17/7.22    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 54.17/7.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 54.17/7.22  fof(f26,plain,(
% 54.17/7.22    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 54.17/7.22    inference(cnf_transformation,[],[f12])).
% 54.17/7.22  fof(f12,axiom,(
% 54.17/7.22    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 54.17/7.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 54.17/7.22  fof(f152253,plain,(
% 54.17/7.22    ( ! [X233,X232] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X232,X233)) = k4_xboole_0(k2_xboole_0(X232,X233),k3_xboole_0(X232,X233))) )),
% 54.17/7.22    inference(forward_demodulation,[],[f152252,f3882])).
% 54.17/7.22  fof(f3882,plain,(
% 54.17/7.22    ( ! [X26,X27,X25] : (k1_xboole_0 = k3_xboole_0(X25,k4_xboole_0(X27,k2_xboole_0(X25,X26)))) )),
% 54.17/7.22    inference(superposition,[],[f2305,f138])).
% 54.17/7.22  fof(f138,plain,(
% 54.17/7.22    ( ! [X2,X1] : (k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1) )),
% 54.17/7.22    inference(forward_demodulation,[],[f130,f95])).
% 54.17/7.22  fof(f95,plain,(
% 54.17/7.22    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 54.17/7.22    inference(superposition,[],[f86,f27])).
% 54.17/7.22  fof(f27,plain,(
% 54.17/7.22    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 54.17/7.22    inference(cnf_transformation,[],[f4])).
% 54.17/7.22  fof(f4,axiom,(
% 54.17/7.22    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 54.17/7.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 54.17/7.22  fof(f86,plain,(
% 54.17/7.22    ( ! [X1] : (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1) )),
% 54.17/7.22    inference(superposition,[],[f70,f24])).
% 54.17/7.22  fof(f24,plain,(
% 54.17/7.22    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 54.17/7.22    inference(cnf_transformation,[],[f1])).
% 54.17/7.22  fof(f1,axiom,(
% 54.17/7.22    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 54.17/7.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 54.17/7.22  fof(f70,plain,(
% 54.17/7.22    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0) )),
% 54.17/7.22    inference(forward_demodulation,[],[f66,f20])).
% 54.17/7.22  fof(f66,plain,(
% 54.17/7.22    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) )),
% 54.17/7.22    inference(superposition,[],[f26,f60])).
% 54.17/7.22  fof(f60,plain,(
% 54.17/7.22    ( ! [X6] : (k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6)) )),
% 54.17/7.22    inference(superposition,[],[f27,f44])).
% 54.17/7.22  fof(f130,plain,(
% 54.17/7.22    ( ! [X2,X1] : (k4_xboole_0(X1,k1_xboole_0) = k3_xboole_0(X1,k2_xboole_0(X1,X2))) )),
% 54.17/7.22    inference(superposition,[],[f28,f22])).
% 54.17/7.22  fof(f28,plain,(
% 54.17/7.22    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 54.17/7.22    inference(cnf_transformation,[],[f9])).
% 54.17/7.22  fof(f9,axiom,(
% 54.17/7.22    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 54.17/7.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 54.17/7.22  fof(f2305,plain,(
% 54.17/7.22    ( ! [X19,X17,X18] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X19,X17),k4_xboole_0(X18,X17))) )),
% 54.17/7.22    inference(superposition,[],[f773,f759])).
% 54.17/7.22  fof(f759,plain,(
% 54.17/7.22    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X8,X7)) = X7) )),
% 54.17/7.22    inference(forward_demodulation,[],[f747,f43])).
% 54.17/7.22  fof(f747,plain,(
% 54.17/7.22    ( ! [X8,X7] : (k5_xboole_0(X7,k1_xboole_0) = k4_xboole_0(X7,k4_xboole_0(X8,X7))) )),
% 54.17/7.22    inference(superposition,[],[f27,f685])).
% 54.17/7.22  fof(f685,plain,(
% 54.17/7.22    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 54.17/7.22    inference(superposition,[],[f30,f289])).
% 54.17/7.22  fof(f289,plain,(
% 54.17/7.22    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X4,X5),X4)) )),
% 54.17/7.22    inference(superposition,[],[f22,f271])).
% 54.17/7.22  fof(f271,plain,(
% 54.17/7.22    ( ! [X4,X3] : (k2_xboole_0(k3_xboole_0(X3,X4),X3) = X3) )),
% 54.17/7.22    inference(superposition,[],[f266,f28])).
% 54.17/7.22  fof(f266,plain,(
% 54.17/7.22    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 54.17/7.22    inference(backward_demodulation,[],[f135,f247])).
% 54.17/7.22  fof(f247,plain,(
% 54.17/7.22    ( ! [X6,X5] : (k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,X6)) = X5) )),
% 54.17/7.22    inference(superposition,[],[f228,f27])).
% 54.17/7.22  fof(f228,plain,(
% 54.17/7.22    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X9,X10),X10) = X9) )),
% 54.17/7.22    inference(superposition,[],[f205,f201])).
% 54.17/7.22  fof(f201,plain,(
% 54.17/7.22    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 54.17/7.22    inference(forward_demodulation,[],[f178,f44])).
% 54.17/7.22  fof(f178,plain,(
% 54.17/7.22    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 54.17/7.22    inference(superposition,[],[f29,f144])).
% 54.17/7.22  fof(f144,plain,(
% 54.17/7.22    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 54.17/7.22    inference(forward_demodulation,[],[f141,f32])).
% 54.17/7.22  fof(f141,plain,(
% 54.17/7.22    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 54.17/7.22    inference(superposition,[],[f27,f137])).
% 54.17/7.22  fof(f137,plain,(
% 54.17/7.22    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 54.17/7.22    inference(forward_demodulation,[],[f129,f95])).
% 54.17/7.22  fof(f129,plain,(
% 54.17/7.22    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 54.17/7.22    inference(superposition,[],[f28,f32])).
% 54.17/7.22  fof(f29,plain,(
% 54.17/7.22    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 54.17/7.22    inference(cnf_transformation,[],[f11])).
% 54.17/7.22  fof(f11,axiom,(
% 54.17/7.22    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 54.17/7.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 54.17/7.22  fof(f205,plain,(
% 54.17/7.22    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 54.17/7.22    inference(superposition,[],[f201,f23])).
% 54.17/7.22  fof(f135,plain,(
% 54.17/7.22    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 54.17/7.22    inference(superposition,[],[f26,f28])).
% 54.17/7.22  fof(f30,plain,(
% 54.17/7.22    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 54.17/7.22    inference(cnf_transformation,[],[f10])).
% 54.17/7.22  fof(f10,axiom,(
% 54.17/7.22    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 54.17/7.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 54.17/7.22  fof(f773,plain,(
% 54.17/7.22    ( ! [X14,X15,X16] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X14,k4_xboole_0(X15,X16)),X16)) )),
% 54.17/7.22    inference(superposition,[],[f740,f30])).
% 54.17/7.22  fof(f740,plain,(
% 54.17/7.22    ( ! [X19,X20] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X20,X19),X19)) )),
% 54.17/7.22    inference(superposition,[],[f685,f401])).
% 54.17/7.22  fof(f401,plain,(
% 54.17/7.22    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) = X6) )),
% 54.17/7.22    inference(forward_demodulation,[],[f400,f138])).
% 54.17/7.22  fof(f400,plain,(
% 54.17/7.22    ( ! [X6,X7] : (k3_xboole_0(X6,k2_xboole_0(X6,X7)) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6))) )),
% 54.17/7.22    inference(forward_demodulation,[],[f391,f24])).
% 54.17/7.22  fof(f391,plain,(
% 54.17/7.22    ( ! [X6,X7] : (k3_xboole_0(k2_xboole_0(X6,X7),X6) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6))) )),
% 54.17/7.22    inference(superposition,[],[f28,f219])).
% 54.17/7.22  fof(f219,plain,(
% 54.17/7.22    ( ! [X6,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),X5) = k4_xboole_0(X6,X5)) )),
% 54.17/7.22    inference(backward_demodulation,[],[f172,f209])).
% 54.17/7.22  fof(f209,plain,(
% 54.17/7.22    ( ! [X12,X11] : (k4_xboole_0(X12,X11) = k5_xboole_0(X11,k2_xboole_0(X11,X12))) )),
% 54.17/7.22    inference(superposition,[],[f201,f26])).
% 54.17/7.22  fof(f172,plain,(
% 54.17/7.22    ( ! [X6,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),X5) = k5_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 54.17/7.22    inference(forward_demodulation,[],[f165,f23])).
% 54.17/7.22  fof(f165,plain,(
% 54.17/7.22    ( ! [X6,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),X5) = k5_xboole_0(k2_xboole_0(X5,X6),X5)) )),
% 54.17/7.22    inference(superposition,[],[f58,f138])).
% 54.17/7.22  fof(f58,plain,(
% 54.17/7.22    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 54.17/7.22    inference(superposition,[],[f27,f24])).
% 54.17/7.22  fof(f152252,plain,(
% 54.17/7.22    ( ! [X233,X232] : (k4_xboole_0(k2_xboole_0(X232,X233),k3_xboole_0(X232,X233)) = k5_xboole_0(k3_xboole_0(X232,k4_xboole_0(X233,k2_xboole_0(X232,X233))),k5_xboole_0(X232,X233))) )),
% 54.17/7.22    inference(forward_demodulation,[],[f151889,f30])).
% 54.17/7.22  fof(f151889,plain,(
% 54.17/7.22    ( ! [X233,X232] : (k4_xboole_0(k2_xboole_0(X232,X233),k3_xboole_0(X232,X233)) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X232,X233),k2_xboole_0(X232,X233)),k5_xboole_0(X232,X233))) )),
% 54.17/7.22    inference(superposition,[],[f106215,f23329])).
% 54.17/7.22  fof(f23329,plain,(
% 54.17/7.22    ( ! [X10,X11] : (k5_xboole_0(X11,X10) = k5_xboole_0(k2_xboole_0(X11,X10),k3_xboole_0(X11,X10))) )),
% 54.17/7.22    inference(superposition,[],[f183,f248])).
% 54.17/7.22  fof(f248,plain,(
% 54.17/7.22    ( ! [X8,X7] : (k5_xboole_0(k4_xboole_0(X7,X8),k3_xboole_0(X8,X7)) = X7) )),
% 54.17/7.22    inference(superposition,[],[f228,f58])).
% 54.17/7.22  fof(f183,plain,(
% 54.17/7.22    ( ! [X14,X15,X16] : (k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X15,X14),X16)) = k5_xboole_0(k2_xboole_0(X14,X15),X16)) )),
% 54.17/7.22    inference(superposition,[],[f29,f26])).
% 54.17/7.22  fof(f106215,plain,(
% 54.17/7.22    ( ! [X21,X22] : (k4_xboole_0(X21,X22) = k5_xboole_0(k4_xboole_0(X22,X21),k5_xboole_0(X21,X22))) )),
% 54.17/7.22    inference(superposition,[],[f205,f13484])).
% 54.17/7.22  fof(f13484,plain,(
% 54.17/7.22    ( ! [X8,X9] : (k5_xboole_0(X8,X9) = k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8))) )),
% 54.17/7.22    inference(superposition,[],[f181,f227])).
% 54.17/7.22  fof(f227,plain,(
% 54.17/7.22    ( ! [X8,X7] : (k5_xboole_0(k3_xboole_0(X8,X7),k4_xboole_0(X7,X8)) = X7) )),
% 54.17/7.22    inference(superposition,[],[f205,f58])).
% 54.17/7.22  fof(f181,plain,(
% 54.17/7.22    ( ! [X10,X8,X9] : (k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = k5_xboole_0(k4_xboole_0(X8,X9),X10)) )),
% 54.17/7.22    inference(superposition,[],[f29,f27])).
% 54.17/7.22  fof(f19,plain,(
% 54.17/7.22    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 54.17/7.22    inference(cnf_transformation,[],[f18])).
% 54.17/7.22  fof(f18,plain,(
% 54.17/7.22    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 54.17/7.22    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 54.17/7.22  fof(f17,plain,(
% 54.17/7.22    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 54.17/7.22    introduced(choice_axiom,[])).
% 54.17/7.22  fof(f16,plain,(
% 54.17/7.22    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 54.17/7.22    inference(ennf_transformation,[],[f14])).
% 54.17/7.22  fof(f14,negated_conjecture,(
% 54.17/7.22    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 54.17/7.22    inference(negated_conjecture,[],[f13])).
% 54.17/7.22  fof(f13,conjecture,(
% 54.17/7.22    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 54.17/7.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 54.17/7.22  % SZS output end Proof for theBenchmark
% 54.17/7.22  % (24306)------------------------------
% 54.17/7.22  % (24306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 54.17/7.22  % (24306)Termination reason: Refutation
% 54.17/7.22  
% 54.17/7.22  % (24306)Memory used [KB]: 176542
% 54.17/7.22  % (24306)Time elapsed: 6.819 s
% 54.17/7.22  % (24306)------------------------------
% 54.17/7.22  % (24306)------------------------------
% 54.73/7.23  % (24289)Success in time 6.876 s
%------------------------------------------------------------------------------

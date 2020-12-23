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
% DateTime   : Thu Dec  3 12:31:57 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 284 expanded)
%              Number of leaves         :   12 (  97 expanded)
%              Depth                    :   18
%              Number of atoms          :   58 ( 285 expanded)
%              Number of equality atoms :   57 ( 284 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1718,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1717,f20])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f1717,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1716,f132])).

fof(f132,plain,(
    ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k2_xboole_0(X4,X5))) ),
    inference(superposition,[],[f91,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f91,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3)) ),
    inference(forward_demodulation,[],[f89,f47])).

fof(f47,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6) ),
    inference(forward_demodulation,[],[f44,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f31,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f19,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f44,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X6,X6) ),
    inference(superposition,[],[f26,f34])).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f24,f20])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f89,plain,(
    ! [X2,X3,X1] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3)) ),
    inference(superposition,[],[f28,f76])).

fof(f76,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f68,f24])).

fof(f68,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f59,f47])).

fof(f59,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f28,f33])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1716,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f1714,f28])).

fof(f1714,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f751,f1713])).

fof(f1713,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X5,X6),X7),k2_xboole_0(X5,X6)) = k4_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f1685,f34])).

fof(f1685,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X5,X6),X7),k2_xboole_0(X5,X6)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X7,k2_xboole_0(X5,X6))) ),
    inference(superposition,[],[f29,f1616])).

fof(f1616,plain,(
    ! [X76,X77] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X76,X77),k2_xboole_0(X76,X77)) ),
    inference(forward_demodulation,[],[f1558,f26])).

fof(f1558,plain,(
    ! [X76,X77] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X76,X77),X77),k2_xboole_0(X76,X77)) ),
    inference(superposition,[],[f1360,f194])).

fof(f194,plain,(
    ! [X24,X25] : k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = X25 ),
    inference(forward_demodulation,[],[f193,f21])).

fof(f193,plain,(
    ! [X24,X25] : k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = k4_xboole_0(X25,k1_xboole_0) ),
    inference(forward_demodulation,[],[f171,f76])).

fof(f171,plain,(
    ! [X24,X25] : k4_xboole_0(X25,k4_xboole_0(X25,k2_xboole_0(X24,X25))) = k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) ),
    inference(superposition,[],[f32,f26])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f25,f25])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1360,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[],[f1233,f32])).

fof(f1233,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9) ),
    inference(superposition,[],[f1091,f194])).

fof(f1091,plain,(
    ! [X21,X22,X20] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(k2_xboole_0(X20,X22),X21)) ),
    inference(superposition,[],[f68,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f751,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f247,f24])).

fof(f247,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f246,f32])).

fof(f246,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) ),
    inference(backward_demodulation,[],[f30,f236])).

fof(f236,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X7,X8) = k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(k4_xboole_0(X6,X7),X8)) ),
    inference(superposition,[],[f28,f194])).

fof(f30,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f18,f25,f27,f27])).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f18,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:22:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.40  % (16372)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.42  % (16381)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.45  % (16369)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.45  % (16368)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.46  % (16376)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.47  % (16378)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.47  % (16385)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.47  % (16373)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.47  % (16375)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.47  % (16367)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.47  % (16371)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.47  % (16380)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.47  % (16384)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.48  % (16383)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.49  % (16374)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.49  % (16382)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.49  % (16366)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.49  % (16379)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.49  % (16379)Refutation not found, incomplete strategy% (16379)------------------------------
% 0.19/0.49  % (16379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (16381)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f1718,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(subsumption_resolution,[],[f1717,f20])).
% 0.19/0.50  fof(f20,plain,(
% 0.19/0.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f5])).
% 0.19/0.50  fof(f5,axiom,(
% 0.19/0.50    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.19/0.50  fof(f1717,plain,(
% 0.19/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0)),
% 0.19/0.50    inference(forward_demodulation,[],[f1716,f132])).
% 0.19/0.50  fof(f132,plain,(
% 0.19/0.50    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k2_xboole_0(X4,X5)))) )),
% 0.19/0.50    inference(superposition,[],[f91,f24])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.19/0.50  fof(f91,plain,(
% 0.19/0.50    ( ! [X2,X3,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f89,f47])).
% 0.19/0.50  fof(f47,plain,(
% 0.19/0.50    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6)) )),
% 0.19/0.50    inference(forward_demodulation,[],[f44,f33])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.19/0.50    inference(backward_demodulation,[],[f31,f21])).
% 0.19/0.50  fof(f21,plain,(
% 0.19/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,axiom,(
% 0.19/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.19/0.50    inference(definition_unfolding,[],[f19,f25])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f11])).
% 0.19/0.50  fof(f11,axiom,(
% 0.19/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f6])).
% 0.19/0.50  fof(f6,axiom,(
% 0.19/0.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.19/0.50  fof(f44,plain,(
% 0.19/0.50    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X6,X6)) )),
% 0.19/0.50    inference(superposition,[],[f26,f34])).
% 0.19/0.50  fof(f34,plain,(
% 0.19/0.50    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.19/0.50    inference(superposition,[],[f24,f20])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f8])).
% 0.19/0.50  fof(f8,axiom,(
% 0.19/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.19/0.50  fof(f89,plain,(
% 0.19/0.50    ( ! [X2,X3,X1] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3))) )),
% 0.19/0.50    inference(superposition,[],[f28,f76])).
% 0.19/0.50  fof(f76,plain,(
% 0.19/0.50    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) )),
% 0.19/0.50    inference(superposition,[],[f68,f24])).
% 0.19/0.50  fof(f68,plain,(
% 0.19/0.50    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f59,f47])).
% 0.19/0.50  fof(f59,plain,(
% 0.19/0.50    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 0.19/0.50    inference(superposition,[],[f28,f33])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.19/0.50  fof(f1716,plain,(
% 0.19/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))))),
% 0.19/0.50    inference(forward_demodulation,[],[f1714,f28])).
% 0.19/0.50  fof(f1714,plain,(
% 0.19/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK1)))),
% 0.19/0.50    inference(backward_demodulation,[],[f751,f1713])).
% 0.19/0.50  fof(f1713,plain,(
% 0.19/0.50    ( ! [X6,X7,X5] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X5,X6),X7),k2_xboole_0(X5,X6)) = k4_xboole_0(X7,k2_xboole_0(X5,X6))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f1685,f34])).
% 0.19/0.50  fof(f1685,plain,(
% 0.19/0.50    ( ! [X6,X7,X5] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X5,X6),X7),k2_xboole_0(X5,X6)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X7,k2_xboole_0(X5,X6)))) )),
% 0.19/0.50    inference(superposition,[],[f29,f1616])).
% 0.19/0.50  fof(f1616,plain,(
% 0.19/0.50    ( ! [X76,X77] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X76,X77),k2_xboole_0(X76,X77))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f1558,f26])).
% 0.19/0.50  fof(f1558,plain,(
% 0.19/0.50    ( ! [X76,X77] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X76,X77),X77),k2_xboole_0(X76,X77))) )),
% 0.19/0.50    inference(superposition,[],[f1360,f194])).
% 0.19/0.50  fof(f194,plain,(
% 0.19/0.50    ( ! [X24,X25] : (k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = X25) )),
% 0.19/0.50    inference(forward_demodulation,[],[f193,f21])).
% 0.19/0.50  fof(f193,plain,(
% 0.19/0.50    ( ! [X24,X25] : (k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = k4_xboole_0(X25,k1_xboole_0)) )),
% 0.19/0.50    inference(forward_demodulation,[],[f171,f76])).
% 0.19/0.50  fof(f171,plain,(
% 0.19/0.50    ( ! [X24,X25] : (k4_xboole_0(X25,k4_xboole_0(X25,k2_xboole_0(X24,X25))) = k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25))) )),
% 0.19/0.50    inference(superposition,[],[f32,f26])).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.19/0.50    inference(definition_unfolding,[],[f23,f25,f25])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.50  fof(f1360,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) )),
% 0.19/0.50    inference(superposition,[],[f1233,f32])).
% 0.19/0.50  fof(f1233,plain,(
% 0.19/0.50    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9)) )),
% 0.19/0.50    inference(superposition,[],[f1091,f194])).
% 0.19/0.50  fof(f1091,plain,(
% 0.19/0.50    ( ! [X21,X22,X20] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(k2_xboole_0(X20,X22),X21))) )),
% 0.19/0.50    inference(superposition,[],[f68,f29])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f10])).
% 0.19/0.50  fof(f10,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 0.19/0.50  fof(f751,plain,(
% 0.19/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)))),
% 0.19/0.50    inference(superposition,[],[f247,f24])).
% 0.19/0.50  fof(f247,plain,(
% 0.19/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.19/0.50    inference(forward_demodulation,[],[f246,f32])).
% 0.19/0.50  fof(f246,plain,(
% 0.19/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))),
% 0.19/0.50    inference(backward_demodulation,[],[f30,f236])).
% 0.19/0.50  fof(f236,plain,(
% 0.19/0.50    ( ! [X6,X8,X7] : (k4_xboole_0(X7,X8) = k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(k4_xboole_0(X6,X7),X8))) )),
% 0.19/0.50    inference(superposition,[],[f28,f194])).
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.19/0.50    inference(definition_unfolding,[],[f18,f25,f27,f27])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.19/0.50    inference(cnf_transformation,[],[f17])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 0.19/0.50  fof(f16,plain,(
% 0.19/0.50    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f15,plain,(
% 0.19/0.50    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.19/0.50    inference(ennf_transformation,[],[f13])).
% 0.19/0.50  fof(f13,negated_conjecture,(
% 0.19/0.50    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.19/0.50    inference(negated_conjecture,[],[f12])).
% 0.19/0.50  fof(f12,conjecture,(
% 0.19/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (16381)------------------------------
% 0.19/0.50  % (16381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (16381)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (16381)Memory used [KB]: 3198
% 0.19/0.50  % (16381)Time elapsed: 0.114 s
% 0.19/0.50  % (16381)------------------------------
% 0.19/0.50  % (16381)------------------------------
% 0.19/0.50  % (16362)Success in time 0.155 s
%------------------------------------------------------------------------------

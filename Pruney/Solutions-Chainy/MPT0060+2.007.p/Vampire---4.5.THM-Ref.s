%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  96 expanded)
%              Number of leaves         :    9 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :   46 (  97 expanded)
%              Number of equality atoms :   45 (  96 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f577,plain,(
    $false ),
    inference(subsumption_resolution,[],[f575,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f575,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f53,f574])).

fof(f574,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f565,f14])).

fof(f14,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f565,plain,(
    ! [X2,X3] : k3_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0) ),
    inference(superposition,[],[f17,f445])).

fof(f445,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),X9) ),
    inference(superposition,[],[f433,f189])).

fof(f189,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k3_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(backward_demodulation,[],[f28,f188])).

fof(f188,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f166,f47])).

fof(f47,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f46,f14])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f31,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f25,f44])).

fof(f44,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(X4,X4) ),
    inference(superposition,[],[f15,f37])).

fof(f37,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f34,f14])).

fof(f34,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f18,f14])).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f15,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f17,f14])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f17,f25])).

% (28835)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
fof(f166,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,X0),X1) ),
    inference(superposition,[],[f28,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f28,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f17,f17])).

fof(f433,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f419,f44])).

fof(f419,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X2) = k4_xboole_0(k3_xboole_0(X2,X3),X2) ),
    inference(superposition,[],[f56,f30])).

fof(f30,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k2_xboole_0(X4,X3)) = X3 ),
    inference(forward_demodulation,[],[f27,f14])).

fof(f27,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k2_xboole_0(X4,X3)) = k4_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f17,f21])).

fof(f21,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f15,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f56,plain,(
    ! [X12,X13,X11] : k4_xboole_0(k3_xboole_0(X13,k2_xboole_0(X11,X12)),X12) = k4_xboole_0(k3_xboole_0(X13,X11),X12) ),
    inference(forward_demodulation,[],[f52,f19])).

fof(f52,plain,(
    ! [X12,X13,X11] : k4_xboole_0(k3_xboole_0(X13,k2_xboole_0(X11,X12)),X12) = k3_xboole_0(X13,k4_xboole_0(X11,X12)) ),
    inference(superposition,[],[f19,f18])).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f53,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK2) ),
    inference(superposition,[],[f13,f19])).

fof(f13,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))
   => k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (28841)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (28838)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (28839)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (28840)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (28849)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (28848)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (28846)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (28846)Refutation not found, incomplete strategy% (28846)------------------------------
% 0.21/0.47  % (28846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (28846)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (28846)Memory used [KB]: 10618
% 0.21/0.47  % (28846)Time elapsed: 0.063 s
% 0.21/0.47  % (28846)------------------------------
% 0.21/0.47  % (28846)------------------------------
% 0.21/0.48  % (28847)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (28838)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f577,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f575,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.48  fof(f575,plain,(
% 0.21/0.48    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 0.21/0.48    inference(backward_demodulation,[],[f53,f574])).
% 0.21/0.48  fof(f574,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f565,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.48  fof(f565,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k3_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0)) )),
% 0.21/0.48    inference(superposition,[],[f17,f445])).
% 0.21/0.48  fof(f445,plain,(
% 0.21/0.48    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),X9)) )),
% 0.21/0.48    inference(superposition,[],[f433,f189])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k3_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 0.21/0.48    inference(backward_demodulation,[],[f28,f188])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f166,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.48    inference(forward_demodulation,[],[f46,f14])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f31,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f25,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(X4,X4)) )),
% 0.21/0.48    inference(superposition,[],[f15,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.21/0.48    inference(forward_demodulation,[],[f34,f14])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 0.21/0.48    inference(superposition,[],[f18,f14])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.21/0.48    inference(superposition,[],[f17,f14])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.48    inference(superposition,[],[f17,f25])).
% 0.21/0.48  % (28835)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,X0),X1)) )),
% 0.21/0.48    inference(superposition,[],[f28,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X6,X5] : (k3_xboole_0(X5,k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k3_xboole_0(X5,X6))) )),
% 0.21/0.48    inference(superposition,[],[f17,f17])).
% 0.21/0.48  fof(f433,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X3),X2)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f419,f44])).
% 0.21/0.48  fof(f419,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k4_xboole_0(X2,X2) = k4_xboole_0(k3_xboole_0(X2,X3),X2)) )),
% 0.21/0.48    inference(superposition,[],[f56,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X4,X3] : (k3_xboole_0(X3,k2_xboole_0(X4,X3)) = X3) )),
% 0.21/0.48    inference(forward_demodulation,[],[f27,f14])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X4,X3] : (k3_xboole_0(X3,k2_xboole_0(X4,X3)) = k4_xboole_0(X3,k1_xboole_0)) )),
% 0.21/0.48    inference(superposition,[],[f17,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 0.21/0.48    inference(superposition,[],[f15,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X12,X13,X11] : (k4_xboole_0(k3_xboole_0(X13,k2_xboole_0(X11,X12)),X12) = k4_xboole_0(k3_xboole_0(X13,X11),X12)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f52,f19])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X12,X13,X11] : (k4_xboole_0(k3_xboole_0(X13,k2_xboole_0(X11,X12)),X12) = k3_xboole_0(X13,k4_xboole_0(X11,X12))) )),
% 0.21/0.48    inference(superposition,[],[f19,f18])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK2)),
% 0.21/0.48    inference(superposition,[],[f13,f19])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) => k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (28838)------------------------------
% 0.21/0.48  % (28838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (28838)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (28838)Memory used [KB]: 2174
% 0.21/0.48  % (28838)Time elapsed: 0.057 s
% 0.21/0.48  % (28838)------------------------------
% 0.21/0.48  % (28838)------------------------------
% 0.21/0.48  % (28834)Success in time 0.126 s
%------------------------------------------------------------------------------

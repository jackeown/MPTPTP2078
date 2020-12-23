%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 208 expanded)
%              Number of leaves         :   10 (  69 expanded)
%              Depth                    :   17
%              Number of atoms          :   51 ( 209 expanded)
%              Number of equality atoms :   50 ( 208 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f338,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f335])).

fof(f335,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(superposition,[],[f22,f321])).

fof(f321,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(backward_demodulation,[],[f238,f319])).

fof(f319,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2) ),
    inference(backward_demodulation,[],[f191,f318])).

fof(f318,plain,(
    ! [X10,X8,X9] : k1_enumset1(X8,X9,X10) = k3_enumset1(X8,X8,X8,X9,X10) ),
    inference(forward_demodulation,[],[f304,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f304,plain,(
    ! [X10,X8,X9] : k3_enumset1(X8,X8,X8,X9,X10) = k2_xboole_0(k1_tarski(X8),k2_tarski(X9,X10)) ),
    inference(superposition,[],[f256,f60])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(superposition,[],[f46,f43])).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(superposition,[],[f28,f23])).

fof(f23,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(forward_demodulation,[],[f44,f23])).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(superposition,[],[f43,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f256,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X2,X3,X4),k2_tarski(X0,X1)) = k3_enumset1(X2,X3,X4,X0,X1) ),
    inference(backward_demodulation,[],[f78,f255])).

fof(f255,plain,(
    ! [X28,X26,X29,X27,X25] : k4_enumset1(X25,X26,X27,X28,X28,X29) = k3_enumset1(X25,X26,X27,X28,X29) ),
    inference(forward_demodulation,[],[f247,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f88,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(forward_demodulation,[],[f75,f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(superposition,[],[f32,f25])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(superposition,[],[f34,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(forward_demodulation,[],[f70,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(superposition,[],[f31,f23])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(f247,plain,(
    ! [X28,X26,X29,X27,X25] : k4_enumset1(X25,X26,X27,X28,X28,X29) = k2_xboole_0(k2_enumset1(X25,X26,X27,X28),k1_tarski(X29)) ),
    inference(superposition,[],[f34,f196])).

fof(f196,plain,(
    ! [X6,X4,X5,X3] : k2_enumset1(X3,X4,X5,X6) = k3_enumset1(X3,X4,X5,X6,X6) ),
    inference(forward_demodulation,[],[f192,f74])).

fof(f192,plain,(
    ! [X6,X4,X5,X3] : k3_enumset1(X3,X4,X5,X6,X6) = k3_enumset1(X3,X3,X4,X5,X6) ),
    inference(superposition,[],[f90,f81])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X1,X2,X3,X4,X0,X0) = k3_enumset1(X1,X2,X3,X4,X0) ),
    inference(backward_demodulation,[],[f87,f89])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X1,X2,X3,X4,X0,X0) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0)) ),
    inference(superposition,[],[f33,f23])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X2,X3,X4,X0,X0,X1) = k2_xboole_0(k1_enumset1(X2,X3,X4),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f32,f25])).

fof(f191,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X1,X2,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(superposition,[],[f90,f82])).

fof(f82,plain,(
    ! [X12,X10,X13,X11] : k4_enumset1(X10,X10,X10,X11,X12,X13) = k2_enumset1(X10,X11,X12,X13) ),
    inference(forward_demodulation,[],[f77,f30])).

fof(f77,plain,(
    ! [X12,X10,X13,X11] : k4_enumset1(X10,X10,X10,X11,X12,X13) = k2_xboole_0(k1_tarski(X10),k1_enumset1(X11,X12,X13)) ),
    inference(superposition,[],[f32,f60])).

fof(f238,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2) ),
    inference(superposition,[],[f196,f74])).

fof(f22,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:28:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (3772)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.46  % (3764)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (3776)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (3765)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (3767)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (3768)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (3771)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (3773)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (3778)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (3774)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (3770)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (3775)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (3766)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (3775)Refutation not found, incomplete strategy% (3775)------------------------------
% 0.21/0.50  % (3775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3775)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (3775)Memory used [KB]: 10490
% 0.21/0.50  % (3775)Time elapsed: 0.085 s
% 0.21/0.50  % (3775)------------------------------
% 0.21/0.50  % (3775)------------------------------
% 0.21/0.50  % (3781)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (3767)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f338,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f335])).
% 0.21/0.50  fof(f335,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)),
% 0.21/0.50    inference(superposition,[],[f22,f321])).
% 0.21/0.50  fof(f321,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f238,f319])).
% 0.21/0.50  fof(f319,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f191,f318])).
% 0.21/0.50  fof(f318,plain,(
% 0.21/0.50    ( ! [X10,X8,X9] : (k1_enumset1(X8,X9,X10) = k3_enumset1(X8,X8,X8,X9,X10)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f304,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.21/0.50  fof(f304,plain,(
% 0.21/0.50    ( ! [X10,X8,X9] : (k3_enumset1(X8,X8,X8,X9,X10) = k2_xboole_0(k1_tarski(X8),k2_tarski(X9,X10))) )),
% 0.21/0.50    inference(superposition,[],[f256,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.50    inference(superposition,[],[f46,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 0.21/0.50    inference(superposition,[],[f28,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f44,f23])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 0.21/0.50    inference(superposition,[],[f43,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X2,X3,X4),k2_tarski(X0,X1)) = k3_enumset1(X2,X3,X4,X0,X1)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f78,f255])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    ( ! [X28,X26,X29,X27,X25] : (k4_enumset1(X25,X26,X27,X28,X28,X29) = k3_enumset1(X25,X26,X27,X28,X29)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f247,f89])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f88,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f75,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.50    inference(superposition,[],[f32,f25])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.21/0.50    inference(superposition,[],[f34,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f70,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.21/0.50    inference(superposition,[],[f31,f23])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    ( ! [X28,X26,X29,X27,X25] : (k4_enumset1(X25,X26,X27,X28,X28,X29) = k2_xboole_0(k2_enumset1(X25,X26,X27,X28),k1_tarski(X29))) )),
% 0.21/0.50    inference(superposition,[],[f34,f196])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    ( ! [X6,X4,X5,X3] : (k2_enumset1(X3,X4,X5,X6) = k3_enumset1(X3,X4,X5,X6,X6)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f192,f74])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    ( ! [X6,X4,X5,X3] : (k3_enumset1(X3,X4,X5,X6,X6) = k3_enumset1(X3,X3,X4,X5,X6)) )),
% 0.21/0.50    inference(superposition,[],[f90,f81])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X1,X2,X3,X4,X0,X0) = k3_enumset1(X1,X2,X3,X4,X0)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f87,f89])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X1,X2,X3,X4,X0,X0) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))) )),
% 0.21/0.50    inference(superposition,[],[f33,f23])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X2,X3,X4,X0,X0,X1) = k2_xboole_0(k1_enumset1(X2,X3,X4),k2_tarski(X0,X1))) )),
% 0.21/0.50    inference(superposition,[],[f32,f25])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X2,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.50    inference(superposition,[],[f90,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X12,X10,X13,X11] : (k4_enumset1(X10,X10,X10,X11,X12,X13) = k2_enumset1(X10,X11,X12,X13)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f77,f30])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X12,X10,X13,X11] : (k4_enumset1(X10,X10,X10,X11,X12,X13) = k2_xboole_0(k1_tarski(X10),k1_enumset1(X11,X12,X13))) )),
% 0.21/0.50    inference(superposition,[],[f32,f60])).
% 0.21/0.50  fof(f238,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)) )),
% 0.21/0.50    inference(superposition,[],[f196,f74])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.50    inference(ennf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.50    inference(negated_conjecture,[],[f17])).
% 0.21/0.50  fof(f17,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (3767)------------------------------
% 0.21/0.50  % (3767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3767)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (3767)Memory used [KB]: 2046
% 0.21/0.50  % (3767)Time elapsed: 0.091 s
% 0.21/0.50  % (3767)------------------------------
% 0.21/0.50  % (3767)------------------------------
% 0.21/0.50  % (3763)Success in time 0.145 s
%------------------------------------------------------------------------------

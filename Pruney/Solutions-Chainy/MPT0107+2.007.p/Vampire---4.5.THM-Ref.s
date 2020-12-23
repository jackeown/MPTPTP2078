%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 165 expanded)
%              Number of leaves         :   11 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :   58 ( 166 expanded)
%              Number of equality atoms :   57 ( 165 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f822,plain,(
    $false ),
    inference(subsumption_resolution,[],[f17,f821])).

fof(f821,plain,(
    ! [X12,X13] : k5_xboole_0(X12,k3_xboole_0(X12,X13)) = k4_xboole_0(X12,X13) ),
    inference(forward_demodulation,[],[f820,f57])).

fof(f57,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f53,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f53,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f49,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f49,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f24,f18])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f820,plain,(
    ! [X12,X13] : k5_xboole_0(X12,k3_xboole_0(X12,X13)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X12,X13)) ),
    inference(forward_demodulation,[],[f819,f19])).

fof(f819,plain,(
    ! [X12,X13] : k5_xboole_0(X12,k3_xboole_0(X12,X13)) = k2_xboole_0(k4_xboole_0(X12,X13),k1_xboole_0) ),
    inference(forward_demodulation,[],[f769,f23])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f769,plain,(
    ! [X12,X13] : k5_xboole_0(X12,k3_xboole_0(X12,X13)) = k2_xboole_0(k4_xboole_0(X12,k3_xboole_0(X12,X13)),k1_xboole_0) ),
    inference(superposition,[],[f26,f353])).

fof(f353,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(backward_demodulation,[],[f276,f335])).

fof(f335,plain,(
    ! [X10] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X10) ),
    inference(backward_demodulation,[],[f232,f331])).

fof(f331,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f315,f57])).

fof(f315,plain,(
    ! [X12,X11] : k2_xboole_0(X11,k4_xboole_0(X11,X12)) = X11 ),
    inference(forward_demodulation,[],[f314,f108])).

fof(f108,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),k3_xboole_0(X3,X4)) = X3 ),
    inference(forward_demodulation,[],[f101,f35])).

fof(f35,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f33,f23])).

fof(f33,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f22,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f101,plain,(
    ! [X4,X3] : k2_xboole_0(k3_xboole_0(X3,k4_xboole_0(X3,X4)),k3_xboole_0(X3,X4)) = X3 ),
    inference(superposition,[],[f25,f22])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f314,plain,(
    ! [X12,X11] : k2_xboole_0(k4_xboole_0(X11,X12),k3_xboole_0(X11,X12)) = k2_xboole_0(X11,k4_xboole_0(X11,X12)) ),
    inference(forward_demodulation,[],[f304,f19])).

fof(f304,plain,(
    ! [X12,X11] : k2_xboole_0(k4_xboole_0(X11,X12),k3_xboole_0(X11,X12)) = k2_xboole_0(k4_xboole_0(X11,X12),X11) ),
    inference(superposition,[],[f55,f25])).

fof(f55,plain,(
    ! [X2,X3] : k2_xboole_0(X3,X2) = k2_xboole_0(X3,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f51,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f51,plain,(
    ! [X2,X3] : k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k5_xboole_0(X3,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f21,f24])).

fof(f232,plain,(
    ! [X10] : k4_xboole_0(k1_xboole_0,X10) = k3_xboole_0(k1_xboole_0,X10) ),
    inference(forward_demodulation,[],[f225,f81])).

fof(f81,plain,(
    ! [X2] : k3_xboole_0(k1_xboole_0,X2) = k3_xboole_0(k3_xboole_0(X2,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f73,f71])).

fof(f71,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f68,f32])).

fof(f32,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f22,f18])).

fof(f68,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f24,f57])).

fof(f73,plain,(
    ! [X2] : k3_xboole_0(k1_xboole_0,X2) = k3_xboole_0(k4_xboole_0(k1_xboole_0,X2),k1_xboole_0) ),
    inference(superposition,[],[f71,f22])).

fof(f225,plain,(
    ! [X10] : k4_xboole_0(k1_xboole_0,X10) = k3_xboole_0(k3_xboole_0(X10,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f71,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f23,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f276,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f275,f20])).

fof(f275,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f268,f32])).

fof(f268,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X0) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f41,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f43,f22])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f22,f23])).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:07:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (5043)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.42  % (5043)Refutation not found, incomplete strategy% (5043)------------------------------
% 0.22/0.42  % (5043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (5043)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.42  
% 0.22/0.42  % (5043)Memory used [KB]: 10490
% 0.22/0.42  % (5043)Time elapsed: 0.004 s
% 0.22/0.42  % (5043)------------------------------
% 0.22/0.42  % (5043)------------------------------
% 0.22/0.46  % (5048)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.47  % (5032)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (5038)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (5048)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f822,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f17,f821])).
% 0.22/0.48  fof(f821,plain,(
% 0.22/0.48    ( ! [X12,X13] : (k5_xboole_0(X12,k3_xboole_0(X12,X13)) = k4_xboole_0(X12,X13)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f820,f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.22/0.48    inference(superposition,[],[f53,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.22/0.48    inference(forward_demodulation,[],[f49,f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 0.22/0.48    inference(superposition,[],[f24,f18])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.22/0.48  fof(f820,plain,(
% 0.22/0.48    ( ! [X12,X13] : (k5_xboole_0(X12,k3_xboole_0(X12,X13)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X12,X13))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f819,f19])).
% 0.22/0.48  fof(f819,plain,(
% 0.22/0.48    ( ! [X12,X13] : (k5_xboole_0(X12,k3_xboole_0(X12,X13)) = k2_xboole_0(k4_xboole_0(X12,X13),k1_xboole_0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f769,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.48  fof(f769,plain,(
% 0.22/0.48    ( ! [X12,X13] : (k5_xboole_0(X12,k3_xboole_0(X12,X13)) = k2_xboole_0(k4_xboole_0(X12,k3_xboole_0(X12,X13)),k1_xboole_0)) )),
% 0.22/0.48    inference(superposition,[],[f26,f353])).
% 0.22/0.48  fof(f353,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.48    inference(backward_demodulation,[],[f276,f335])).
% 0.22/0.48  fof(f335,plain,(
% 0.22/0.48    ( ! [X10] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X10)) )),
% 0.22/0.48    inference(backward_demodulation,[],[f232,f331])).
% 0.22/0.48  fof(f331,plain,(
% 0.22/0.48    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6)) )),
% 0.22/0.48    inference(superposition,[],[f315,f57])).
% 0.22/0.48  fof(f315,plain,(
% 0.22/0.48    ( ! [X12,X11] : (k2_xboole_0(X11,k4_xboole_0(X11,X12)) = X11) )),
% 0.22/0.48    inference(forward_demodulation,[],[f314,f108])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),k3_xboole_0(X3,X4)) = X3) )),
% 0.22/0.48    inference(forward_demodulation,[],[f101,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f33,f23])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(superposition,[],[f22,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    ( ! [X4,X3] : (k2_xboole_0(k3_xboole_0(X3,k4_xboole_0(X3,X4)),k3_xboole_0(X3,X4)) = X3) )),
% 0.22/0.48    inference(superposition,[],[f25,f22])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.48  fof(f314,plain,(
% 0.22/0.48    ( ! [X12,X11] : (k2_xboole_0(k4_xboole_0(X11,X12),k3_xboole_0(X11,X12)) = k2_xboole_0(X11,k4_xboole_0(X11,X12))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f304,f19])).
% 0.22/0.48  fof(f304,plain,(
% 0.22/0.48    ( ! [X12,X11] : (k2_xboole_0(k4_xboole_0(X11,X12),k3_xboole_0(X11,X12)) = k2_xboole_0(k4_xboole_0(X11,X12),X11)) )),
% 0.22/0.48    inference(superposition,[],[f55,f25])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = k2_xboole_0(X3,k2_xboole_0(X2,X3))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f51,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X2,X3] : (k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k5_xboole_0(X3,k4_xboole_0(X2,X3))) )),
% 0.22/0.48    inference(superposition,[],[f21,f24])).
% 0.22/0.48  fof(f232,plain,(
% 0.22/0.48    ( ! [X10] : (k4_xboole_0(k1_xboole_0,X10) = k3_xboole_0(k1_xboole_0,X10)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f225,f81])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    ( ! [X2] : (k3_xboole_0(k1_xboole_0,X2) = k3_xboole_0(k3_xboole_0(X2,k1_xboole_0),k1_xboole_0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f73,f71])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f68,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.22/0.48    inference(superposition,[],[f22,f18])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.48    inference(superposition,[],[f24,f57])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ( ! [X2] : (k3_xboole_0(k1_xboole_0,X2) = k3_xboole_0(k4_xboole_0(k1_xboole_0,X2),k1_xboole_0)) )),
% 0.22/0.48    inference(superposition,[],[f71,f22])).
% 0.22/0.48  fof(f225,plain,(
% 0.22/0.48    ( ! [X10] : (k4_xboole_0(k1_xboole_0,X10) = k3_xboole_0(k3_xboole_0(X10,k1_xboole_0),k1_xboole_0)) )),
% 0.22/0.48    inference(superposition,[],[f71,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 0.22/0.48    inference(superposition,[],[f23,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.48  fof(f276,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f275,f20])).
% 0.22/0.48  fof(f275,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f268,f32])).
% 0.22/0.48  fof(f268,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X0) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(superposition,[],[f41,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f43,f22])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(superposition,[],[f22,f23])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.48    inference(negated_conjecture,[],[f12])).
% 0.22/0.48  fof(f12,conjecture,(
% 0.22/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (5048)------------------------------
% 0.22/0.48  % (5048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (5048)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (5048)Memory used [KB]: 6524
% 0.22/0.48  % (5048)Time elapsed: 0.051 s
% 0.22/0.48  % (5048)------------------------------
% 0.22/0.48  % (5048)------------------------------
% 0.22/0.48  % (5036)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (5041)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (5031)Success in time 0.124 s
%------------------------------------------------------------------------------

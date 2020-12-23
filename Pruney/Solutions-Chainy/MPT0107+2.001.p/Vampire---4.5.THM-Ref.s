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
% DateTime   : Thu Dec  3 12:32:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 340 expanded)
%              Number of leaves         :   13 ( 118 expanded)
%              Depth                    :   16
%              Number of atoms          :   61 ( 341 expanded)
%              Number of equality atoms :   60 ( 340 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1296,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1295,f69])).

fof(f69,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f55,f47])).

fof(f47,plain,(
    ! [X1] : k5_xboole_0(o_0_0_xboole_0,X1) = X1 ),
    inference(superposition,[],[f29,f38])).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f23,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(o_0_0_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f34,f37])).

fof(f37,plain,(
    ! [X0] : o_0_0_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1295,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f997,f1242])).

fof(f1242,plain,(
    ! [X28,X27] : k5_xboole_0(X28,k4_xboole_0(X28,X27)) = k5_xboole_0(X27,k4_xboole_0(X27,X28)) ),
    inference(superposition,[],[f91,f1046])).

fof(f1046,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(backward_demodulation,[],[f461,f1042])).

fof(f1042,plain,(
    ! [X19,X18] : k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k5_xboole_0(X18,k4_xboole_0(X18,X19)) ),
    inference(forward_demodulation,[],[f1027,f29])).

fof(f1027,plain,(
    ! [X19,X18] : k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k5_xboole_0(k4_xboole_0(X18,X19),X18) ),
    inference(superposition,[],[f73,f464])).

fof(f464,plain,(
    ! [X8,X9] : k5_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = X8 ),
    inference(forward_demodulation,[],[f463,f38])).

fof(f463,plain,(
    ! [X8,X9] : k5_xboole_0(X8,o_0_0_xboole_0) = k5_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f448,f459])).

fof(f459,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(backward_demodulation,[],[f251,f442])).

fof(f442,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f43,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f28,f32,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f251,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0) ),
    inference(superposition,[],[f243,f41])).

fof(f243,plain,(
    ! [X12,X11] : o_0_0_xboole_0 = k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11) ),
    inference(forward_demodulation,[],[f237,f37])).

fof(f237,plain,(
    ! [X12,X11] : k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11) = k5_xboole_0(X11,X11) ),
    inference(superposition,[],[f69,f42])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(definition_unfolding,[],[f30,f31,f32])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f448,plain,(
    ! [X8,X9] : k5_xboole_0(X8,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X8)) = k5_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) ),
    inference(superposition,[],[f40,f43])).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f27,f31,f31])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f73,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f69,f29])).

fof(f461,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(forward_demodulation,[],[f460,f38])).

fof(f460,plain,(
    ! [X0,X1] : k5_xboole_0(X0,o_0_0_xboole_0) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(backward_demodulation,[],[f218,f459])).

fof(f218,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f40,f41])).

fof(f91,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f73,f73])).

fof(f997,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0))) ),
    inference(forward_demodulation,[],[f996,f29])).

fof(f996,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),sK1)) ),
    inference(backward_demodulation,[],[f36,f952])).

fof(f952,plain,(
    ! [X19,X18] : k5_xboole_0(k4_xboole_0(X18,X19),X18) = k4_xboole_0(X19,k4_xboole_0(X19,X18)) ),
    inference(superposition,[],[f69,f461])).

fof(f36,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f22,f32])).

fof(f22,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (24983)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.45  % (24983)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f1296,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(subsumption_resolution,[],[f1295,f69])).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.20/0.45    inference(forward_demodulation,[],[f55,f47])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    ( ! [X1] : (k5_xboole_0(o_0_0_xboole_0,X1) = X1) )),
% 0.20/0.45    inference(superposition,[],[f29,f38])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ( ! [X0] : (k5_xboole_0(X0,o_0_0_xboole_0) = X0) )),
% 0.20/0.45    inference(definition_unfolding,[],[f25,f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    k1_xboole_0 = o_0_0_xboole_0),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    k1_xboole_0 = o_0_0_xboole_0),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,axiom,(
% 0.20/0.45    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k5_xboole_0(o_0_0_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.20/0.45    inference(superposition,[],[f34,f37])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ( ! [X0] : (o_0_0_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f24,f23])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,axiom,(
% 0.20/0.45    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.45  fof(f1295,plain,(
% 0.20/0.45    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.45    inference(backward_demodulation,[],[f997,f1242])).
% 0.20/0.45  fof(f1242,plain,(
% 0.20/0.45    ( ! [X28,X27] : (k5_xboole_0(X28,k4_xboole_0(X28,X27)) = k5_xboole_0(X27,k4_xboole_0(X27,X28))) )),
% 0.20/0.45    inference(superposition,[],[f91,f1046])).
% 0.20/0.45  fof(f1046,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X1,X0))) = X0) )),
% 0.20/0.45    inference(backward_demodulation,[],[f461,f1042])).
% 0.20/0.45  fof(f1042,plain,(
% 0.20/0.45    ( ! [X19,X18] : (k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k5_xboole_0(X18,k4_xboole_0(X18,X19))) )),
% 0.20/0.45    inference(forward_demodulation,[],[f1027,f29])).
% 0.20/0.45  fof(f1027,plain,(
% 0.20/0.45    ( ! [X19,X18] : (k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k5_xboole_0(k4_xboole_0(X18,X19),X18)) )),
% 0.20/0.45    inference(superposition,[],[f73,f464])).
% 0.20/0.45  fof(f464,plain,(
% 0.20/0.45    ( ! [X8,X9] : (k5_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = X8) )),
% 0.20/0.45    inference(forward_demodulation,[],[f463,f38])).
% 0.20/0.45  fof(f463,plain,(
% 0.20/0.45    ( ! [X8,X9] : (k5_xboole_0(X8,o_0_0_xboole_0) = k5_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9))) )),
% 0.20/0.45    inference(forward_demodulation,[],[f448,f459])).
% 0.20/0.45  fof(f459,plain,(
% 0.20/0.45    ( ! [X0,X1] : (o_0_0_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.45    inference(backward_demodulation,[],[f251,f442])).
% 0.20/0.45  fof(f442,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.20/0.45    inference(superposition,[],[f43,f41])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f28,f32,f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,axiom,(
% 0.20/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f33,f32])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,axiom,(
% 0.20/0.45    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.45  fof(f251,plain,(
% 0.20/0.45    ( ! [X0,X1] : (o_0_0_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0)) )),
% 0.20/0.45    inference(superposition,[],[f243,f41])).
% 0.20/0.45  fof(f243,plain,(
% 0.20/0.45    ( ! [X12,X11] : (o_0_0_xboole_0 = k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11)) )),
% 0.20/0.45    inference(forward_demodulation,[],[f237,f37])).
% 0.20/0.45  fof(f237,plain,(
% 0.20/0.45    ( ! [X12,X11] : (k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11) = k5_xboole_0(X11,X11)) )),
% 0.20/0.45    inference(superposition,[],[f69,f42])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 0.20/0.45    inference(definition_unfolding,[],[f30,f31,f32])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,axiom,(
% 0.20/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.20/0.45  fof(f448,plain,(
% 0.20/0.45    ( ! [X8,X9] : (k5_xboole_0(X8,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X8)) = k5_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9))) )),
% 0.20/0.45    inference(superposition,[],[f40,f43])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f27,f31,f31])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 0.20/0.45    inference(superposition,[],[f69,f29])).
% 0.20/0.45  fof(f461,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0) )),
% 0.20/0.45    inference(forward_demodulation,[],[f460,f38])).
% 0.20/0.45  fof(f460,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k5_xboole_0(X0,o_0_0_xboole_0) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.20/0.45    inference(backward_demodulation,[],[f218,f459])).
% 0.20/0.45  fof(f218,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.20/0.45    inference(superposition,[],[f40,f41])).
% 0.20/0.45  fof(f91,plain,(
% 0.20/0.45    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 0.20/0.45    inference(superposition,[],[f73,f73])).
% 0.20/0.45  fof(f997,plain,(
% 0.20/0.45    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0)))),
% 0.20/0.45    inference(forward_demodulation,[],[f996,f29])).
% 0.20/0.45  fof(f996,plain,(
% 0.20/0.45    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),sK1))),
% 0.20/0.45    inference(backward_demodulation,[],[f36,f952])).
% 0.20/0.45  fof(f952,plain,(
% 0.20/0.45    ( ! [X19,X18] : (k5_xboole_0(k4_xboole_0(X18,X19),X18) = k4_xboole_0(X19,k4_xboole_0(X19,X18))) )),
% 0.20/0.45    inference(superposition,[],[f69,f461])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.45    inference(definition_unfolding,[],[f22,f32])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.45    inference(negated_conjecture,[],[f14])).
% 0.20/0.45  fof(f14,conjecture,(
% 0.20/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (24983)------------------------------
% 0.20/0.45  % (24983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (24983)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (24983)Memory used [KB]: 2814
% 0.20/0.45  % (24983)Time elapsed: 0.043 s
% 0.20/0.45  % (24983)------------------------------
% 0.20/0.45  % (24983)------------------------------
% 0.20/0.45  % (24969)Success in time 0.097 s
%------------------------------------------------------------------------------

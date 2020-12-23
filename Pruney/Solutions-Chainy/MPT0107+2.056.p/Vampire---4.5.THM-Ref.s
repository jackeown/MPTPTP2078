%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 110 expanded)
%              Number of leaves         :   10 (  37 expanded)
%              Depth                    :   15
%              Number of atoms          :   44 ( 111 expanded)
%              Number of equality atoms :   43 ( 110 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1579,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1578,f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f1578,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f33,f1528])).

fof(f1528,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(superposition,[],[f1428,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f1428,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ),
    inference(backward_demodulation,[],[f153,f1425])).

fof(f1425,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(forward_demodulation,[],[f1424,f584])).

fof(f584,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f583,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f583,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f582,f18])).

fof(f582,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f523,f20])).

fof(f20,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f523,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k2_xboole_0(X0,X0))) ),
    inference(superposition,[],[f32,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f20,f18])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k2_xboole_0(X0,X0))) ),
    inference(backward_demodulation,[],[f27,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f1424,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))),k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f1372,f25])).

fof(f1372,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f585,f29])).

fof(f585,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
    inference(backward_demodulation,[],[f32,f584])).

fof(f153,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f43,f29])).

fof(f43,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9))) ),
    inference(superposition,[],[f25,f35])).

fof(f33,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))) ),
    inference(backward_demodulation,[],[f31,f25])).

fof(f31,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)) ),
    inference(backward_demodulation,[],[f28,f29])).

fof(f28,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)) ),
    inference(definition_unfolding,[],[f16,f24,f21])).

fof(f16,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (3984)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.44  % (3984)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f1579,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(subsumption_resolution,[],[f1578,f18])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.44  fof(f1578,plain,(
% 0.20/0.44    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.20/0.44    inference(backward_demodulation,[],[f33,f1528])).
% 0.20/0.44  fof(f1528,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0))) )),
% 0.20/0.44    inference(superposition,[],[f1428,f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f23,f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.44  fof(f1428,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) )),
% 0.20/0.44    inference(backward_demodulation,[],[f153,f1425])).
% 0.20/0.44  fof(f1425,plain,(
% 0.20/0.44    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)) )),
% 0.20/0.44    inference(forward_demodulation,[],[f1424,f584])).
% 0.20/0.44  fof(f584,plain,(
% 0.20/0.44    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.44    inference(forward_demodulation,[],[f583,f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.44  fof(f583,plain,(
% 0.20/0.44    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,X0)) )),
% 0.20/0.44    inference(forward_demodulation,[],[f582,f18])).
% 0.20/0.44  fof(f582,plain,(
% 0.20/0.44    ( ! [X0] : (k2_xboole_0(X0,X0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0)) )),
% 0.20/0.44    inference(forward_demodulation,[],[f523,f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.44  fof(f523,plain,(
% 0.20/0.44    ( ! [X0] : (k2_xboole_0(X0,X0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k2_xboole_0(X0,X0)))) )),
% 0.20/0.44    inference(superposition,[],[f32,f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.44    inference(superposition,[],[f20,f18])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k2_xboole_0(X0,X0)))) )),
% 0.20/0.44    inference(backward_demodulation,[],[f27,f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f22,f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.44  fof(f1424,plain,(
% 0.20/0.44    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))),k4_xboole_0(X1,X2))) )),
% 0.20/0.44    inference(forward_demodulation,[],[f1372,f25])).
% 0.20/0.44  fof(f1372,plain,(
% 0.20/0.44    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))) )),
% 0.20/0.44    inference(superposition,[],[f585,f29])).
% 0.20/0.44  fof(f585,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) )),
% 0.20/0.44    inference(backward_demodulation,[],[f32,f584])).
% 0.20/0.44  fof(f153,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)))) )),
% 0.20/0.44    inference(superposition,[],[f43,f29])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9)))) )),
% 0.20/0.44    inference(superposition,[],[f25,f35])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)))),
% 0.20/0.44    inference(backward_demodulation,[],[f31,f25])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),
% 0.20/0.44    inference(backward_demodulation,[],[f28,f29])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),
% 0.20/0.44    inference(definition_unfolding,[],[f16,f24,f21])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.44    inference(cnf_transformation,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.44    inference(negated_conjecture,[],[f11])).
% 0.20/0.44  fof(f11,conjecture,(
% 0.20/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (3984)------------------------------
% 0.20/0.44  % (3984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (3984)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (3984)Memory used [KB]: 2814
% 0.20/0.44  % (3984)Time elapsed: 0.039 s
% 0.20/0.44  % (3984)------------------------------
% 0.20/0.44  % (3984)------------------------------
% 0.20/0.45  % (3970)Success in time 0.092 s
%------------------------------------------------------------------------------

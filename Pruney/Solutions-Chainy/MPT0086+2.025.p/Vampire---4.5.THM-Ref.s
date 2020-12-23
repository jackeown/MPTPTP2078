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
% DateTime   : Thu Dec  3 12:31:27 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   37 (  65 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :   12
%              Number of atoms          :   44 (  72 expanded)
%              Number of equality atoms :   31 (  59 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f251,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f250])).

fof(f250,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f236,f27])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f23,f16])).

fof(f16,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f15,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f236,plain,(
    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f29,f234])).

fof(f234,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = X1 ),
    inference(forward_demodulation,[],[f202,f16])).

fof(f202,plain,(
    ! [X1] : k2_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(superposition,[],[f102,f27])).

fof(f102,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(forward_demodulation,[],[f101,f16])).

fof(f101,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f82,f42])).

fof(f42,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f32,f17])).

fof(f17,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f32,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f21,f27])).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f82,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f26,f16])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f22,f18])).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f29,plain,(
    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f28,f21])).

fof(f28,plain,(
    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) ),
    inference(resolution,[],[f24,f14])).

fof(f14,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1)
   => ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f20,f18])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.10  % Command    : run_vampire %s %d
% 0.10/0.31  % Computer   : n005.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 15:31:17 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.37  % (13095)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.16/0.38  % (13093)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.16/0.38  % (13093)Refutation found. Thanks to Tanya!
% 0.16/0.38  % SZS status Theorem for theBenchmark
% 0.16/0.38  % SZS output start Proof for theBenchmark
% 0.16/0.38  fof(f251,plain,(
% 0.16/0.38    $false),
% 0.16/0.38    inference(trivial_inequality_removal,[],[f250])).
% 0.16/0.38  fof(f250,plain,(
% 0.16/0.38    k1_xboole_0 != k1_xboole_0),
% 0.16/0.38    inference(superposition,[],[f236,f27])).
% 0.16/0.38  fof(f27,plain,(
% 0.16/0.38    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.16/0.38    inference(backward_demodulation,[],[f23,f16])).
% 0.16/0.38  fof(f16,plain,(
% 0.16/0.38    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.16/0.38    inference(cnf_transformation,[],[f3])).
% 0.16/0.38  fof(f3,axiom,(
% 0.16/0.38    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.16/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.16/0.38  fof(f23,plain,(
% 0.16/0.38    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.16/0.38    inference(definition_unfolding,[],[f15,f18])).
% 0.16/0.38  fof(f18,plain,(
% 0.16/0.38    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.16/0.38    inference(cnf_transformation,[],[f6])).
% 0.16/0.38  fof(f6,axiom,(
% 0.16/0.38    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.16/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.16/0.38  fof(f15,plain,(
% 0.16/0.38    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.16/0.38    inference(cnf_transformation,[],[f2])).
% 0.16/0.38  fof(f2,axiom,(
% 0.16/0.38    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.16/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.16/0.38  fof(f236,plain,(
% 0.16/0.38    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.16/0.38    inference(backward_demodulation,[],[f29,f234])).
% 0.16/0.38  fof(f234,plain,(
% 0.16/0.38    ( ! [X1] : (k2_xboole_0(X1,X1) = X1) )),
% 0.16/0.38    inference(forward_demodulation,[],[f202,f16])).
% 0.16/0.38  fof(f202,plain,(
% 0.16/0.38    ( ! [X1] : (k2_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = X1) )),
% 0.16/0.38    inference(superposition,[],[f102,f27])).
% 0.16/0.38  fof(f102,plain,(
% 0.16/0.38    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 0.16/0.38    inference(forward_demodulation,[],[f101,f16])).
% 0.16/0.38  fof(f101,plain,(
% 0.16/0.38    ( ! [X0,X1] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.16/0.38    inference(forward_demodulation,[],[f82,f42])).
% 0.16/0.38  fof(f42,plain,(
% 0.16/0.38    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)) )),
% 0.16/0.38    inference(forward_demodulation,[],[f32,f17])).
% 0.16/0.38  fof(f17,plain,(
% 0.16/0.38    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.16/0.38    inference(cnf_transformation,[],[f5])).
% 0.16/0.38  fof(f5,axiom,(
% 0.16/0.38    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.16/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.16/0.38  fof(f32,plain,(
% 0.16/0.38    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 0.16/0.38    inference(superposition,[],[f21,f27])).
% 0.16/0.38  fof(f21,plain,(
% 0.16/0.38    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.16/0.38    inference(cnf_transformation,[],[f4])).
% 0.16/0.38  fof(f4,axiom,(
% 0.16/0.38    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.16/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.16/0.38  fof(f82,plain,(
% 0.16/0.38    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.16/0.38    inference(superposition,[],[f26,f16])).
% 0.16/0.38  fof(f26,plain,(
% 0.16/0.38    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.16/0.38    inference(definition_unfolding,[],[f22,f18])).
% 0.16/0.38  fof(f22,plain,(
% 0.16/0.38    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.16/0.38    inference(cnf_transformation,[],[f7])).
% 0.16/0.38  fof(f7,axiom,(
% 0.16/0.38    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.16/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.16/0.38  fof(f29,plain,(
% 0.16/0.38    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,sK1)))),
% 0.16/0.38    inference(forward_demodulation,[],[f28,f21])).
% 0.16/0.38  fof(f28,plain,(
% 0.16/0.38    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))),
% 0.16/0.38    inference(resolution,[],[f24,f14])).
% 0.16/0.38  fof(f14,plain,(
% 0.16/0.38    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.16/0.38    inference(cnf_transformation,[],[f12])).
% 0.16/0.38  fof(f12,plain,(
% 0.16/0.38    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.16/0.38    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 0.16/0.38  fof(f11,plain,(
% 0.16/0.38    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),X1) => ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.16/0.38    introduced(choice_axiom,[])).
% 0.16/0.38  fof(f10,plain,(
% 0.16/0.38    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.16/0.38    inference(ennf_transformation,[],[f9])).
% 0.16/0.38  fof(f9,negated_conjecture,(
% 0.16/0.38    ~! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.16/0.38    inference(negated_conjecture,[],[f8])).
% 0.16/0.38  fof(f8,conjecture,(
% 0.16/0.38    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.16/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.16/0.38  fof(f24,plain,(
% 0.16/0.38    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.16/0.38    inference(definition_unfolding,[],[f20,f18])).
% 0.16/0.38  fof(f20,plain,(
% 0.16/0.38    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.16/0.38    inference(cnf_transformation,[],[f13])).
% 0.16/0.38  fof(f13,plain,(
% 0.16/0.38    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.16/0.38    inference(nnf_transformation,[],[f1])).
% 0.16/0.38  fof(f1,axiom,(
% 0.16/0.38    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.16/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.16/0.38  % SZS output end Proof for theBenchmark
% 0.16/0.38  % (13093)------------------------------
% 0.16/0.38  % (13093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.38  % (13093)Termination reason: Refutation
% 0.16/0.38  
% 0.16/0.38  % (13093)Memory used [KB]: 1791
% 0.16/0.38  % (13093)Time elapsed: 0.029 s
% 0.16/0.38  % (13093)------------------------------
% 0.16/0.38  % (13093)------------------------------
% 0.16/0.38  % (13091)Success in time 0.066 s
%------------------------------------------------------------------------------

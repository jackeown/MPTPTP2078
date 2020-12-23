%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   10 (  13 expanded)
%              Depth                    :   12
%              Number of atoms          :   44 (  58 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(resolution,[],[f69,f26])).

fof(f26,plain,(
    ~ r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f23,f15])).

fof(f15,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) )
   => ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X0)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_xboole_0 = k4_xboole_0(X1,X0)
          & r2_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( k1_xboole_0 = k4_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f69,plain,(
    r1_tarski(sK1,sK0) ),
    inference(superposition,[],[f19,f64])).

fof(f64,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f59,f18])).

fof(f18,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f59,plain,(
    k3_xboole_0(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f58,f17])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f58,plain,(
    ! [X16] : k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),X16)) = X16 ),
    inference(forward_demodulation,[],[f46,f32])).

fof(f32,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f21,f18])).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f46,plain,(
    ! [X16] : k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),X16)) = k5_xboole_0(k1_xboole_0,X16) ),
    inference(superposition,[],[f24,f27])).

fof(f27,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f25,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f25,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)) ),
    inference(definition_unfolding,[],[f16,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f16,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:50:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (23138)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.42  % (23138)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(resolution,[],[f69,f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ~r1_tarski(sK1,sK0)),
% 0.21/0.42    inference(resolution,[],[f23,f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    r2_xboole_0(sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    k1_xboole_0 = k4_xboole_0(sK1,sK0) & r2_xboole_0(sK0,sK1)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1)) => (k1_xboole_0 = k4_xboole_0(sK1,sK0) & r2_xboole_0(sK0,sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : ~(k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.21/0.42    inference(negated_conjecture,[],[f9])).
% 0.21/0.42  fof(f9,conjecture,(
% 0.21/0.42    ! [X0,X1] : ~(k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    r1_tarski(sK1,sK0)),
% 0.21/0.42    inference(superposition,[],[f19,f64])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    sK1 = k3_xboole_0(sK0,sK1)),
% 0.21/0.42    inference(forward_demodulation,[],[f59,f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    k3_xboole_0(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.42    inference(superposition,[],[f58,f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,axiom,(
% 0.21/0.42    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    ( ! [X16] : (k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),X16)) = X16) )),
% 0.21/0.42    inference(forward_demodulation,[],[f46,f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.21/0.42    inference(superposition,[],[f21,f18])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    ( ! [X16] : (k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),X16)) = k5_xboole_0(k1_xboole_0,X16)) )),
% 0.21/0.42    inference(superposition,[],[f24,f27])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),
% 0.21/0.42    inference(backward_demodulation,[],[f25,f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),
% 0.21/0.42    inference(definition_unfolding,[],[f16,f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (23138)------------------------------
% 0.21/0.42  % (23138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (23138)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (23138)Memory used [KB]: 6140
% 0.21/0.42  % (23138)Time elapsed: 0.006 s
% 0.21/0.42  % (23138)------------------------------
% 0.21/0.42  % (23138)------------------------------
% 0.21/0.42  % (23130)Success in time 0.062 s
%------------------------------------------------------------------------------

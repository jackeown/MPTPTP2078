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
% DateTime   : Thu Dec  3 12:32:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 103 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :   16
%              Number of atoms          :   67 ( 122 expanded)
%              Number of equality atoms :   51 (  97 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f120,plain,(
    $false ),
    inference(subsumption_resolution,[],[f111,f36])).

fof(f36,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f111,plain,(
    r2_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f17,f104])).

fof(f104,plain,(
    sK0 = sK1 ),
    inference(superposition,[],[f96,f21])).

fof(f21,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f96,plain,(
    sK0 = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f92,f20])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f92,plain,(
    ! [X18] : k5_xboole_0(sK1,k5_xboole_0(sK0,X18)) = X18 ),
    inference(forward_demodulation,[],[f90,f77])).

fof(f77,plain,(
    ! [X8,X9] : k5_xboole_0(X8,k5_xboole_0(k2_xboole_0(X8,k1_xboole_0),X9)) = X9 ),
    inference(forward_demodulation,[],[f60,f43])).

fof(f43,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f22,f21])).

fof(f22,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f60,plain,(
    ! [X8,X9] : k5_xboole_0(X8,k5_xboole_0(k2_xboole_0(X8,k1_xboole_0),X9)) = k5_xboole_0(k1_xboole_0,X9) ),
    inference(superposition,[],[f31,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f34,f21])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k2_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f19,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f31,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f90,plain,(
    ! [X18] : k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(sK1,k1_xboole_0),X18)))) = X18 ),
    inference(backward_demodulation,[],[f82,f89])).

fof(f89,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f84,f20])).

fof(f84,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f76,f55])).

fof(f55,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f54,f17])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(resolution,[],[f26,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X1,X0))) ),
    inference(backward_demodulation,[],[f40,f75])).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f57,f43])).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f31,f20])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k2_xboole_0(X1,X0))))) ),
    inference(backward_demodulation,[],[f35,f31])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f24,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f25])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f82,plain,(
    ! [X18] : k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(sK1,sK0),X18)))) = X18 ),
    inference(forward_demodulation,[],[f81,f31])).

fof(f81,plain,(
    ! [X18] : k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK1,sK0)),X18))) = X18 ),
    inference(forward_demodulation,[],[f80,f31])).

fof(f80,plain,(
    ! [X18] : k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK1,sK0))),X18)) = X18 ),
    inference(forward_demodulation,[],[f64,f43])).

fof(f64,plain,(
    ! [X18] : k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK1,sK0))),X18)) = k5_xboole_0(k1_xboole_0,X18) ),
    inference(superposition,[],[f31,f39])).

fof(f39,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f38,f31])).

fof(f38,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0))) ),
    inference(backward_demodulation,[],[f33,f22])).

fof(f33,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0))) ),
    inference(definition_unfolding,[],[f18,f32])).

fof(f18,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X0)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_xboole_0 = k4_xboole_0(X1,X0)
          & r2_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ~ ( k1_xboole_0 = k4_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

fof(f17,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:51:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (24648)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.47  % (24648)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f111,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.21/0.47    inference(equality_resolution,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    r2_xboole_0(sK0,sK0)),
% 0.21/0.47    inference(backward_demodulation,[],[f17,f104])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    sK0 = sK1),
% 0.21/0.47    inference(superposition,[],[f96,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    sK0 = k5_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.47    inference(superposition,[],[f92,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ( ! [X18] : (k5_xboole_0(sK1,k5_xboole_0(sK0,X18)) = X18) )),
% 0.21/0.47    inference(forward_demodulation,[],[f90,f77])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ( ! [X8,X9] : (k5_xboole_0(X8,k5_xboole_0(k2_xboole_0(X8,k1_xboole_0),X9)) = X9) )),
% 0.21/0.47    inference(forward_demodulation,[],[f60,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.21/0.47    inference(superposition,[],[f22,f21])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X8,X9] : (k5_xboole_0(X8,k5_xboole_0(k2_xboole_0(X8,k1_xboole_0),X9)) = k5_xboole_0(k1_xboole_0,X9)) )),
% 0.21/0.47    inference(superposition,[],[f31,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.47    inference(backward_demodulation,[],[f34,f21])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k2_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f19,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ( ! [X18] : (k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(sK1,k1_xboole_0),X18)))) = X18) )),
% 0.21/0.47    inference(backward_demodulation,[],[f82,f89])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.47    inference(forward_demodulation,[],[f84,f20])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k5_xboole_0(sK1,sK1))),
% 0.21/0.47    inference(superposition,[],[f76,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    sK1 = k2_xboole_0(sK0,sK1)),
% 0.21/0.47    inference(resolution,[],[f54,f17])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.47    inference(resolution,[],[f26,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X1,X0)))) )),
% 0.21/0.47    inference(backward_demodulation,[],[f40,f75])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.21/0.47    inference(forward_demodulation,[],[f57,f43])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(superposition,[],[f31,f20])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k2_xboole_0(X1,X0)))))) )),
% 0.21/0.47    inference(backward_demodulation,[],[f35,f31])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0))))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f24,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f23,f25])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ( ! [X18] : (k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(sK1,sK0),X18)))) = X18) )),
% 0.21/0.47    inference(forward_demodulation,[],[f81,f31])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ( ! [X18] : (k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK1,sK0)),X18))) = X18) )),
% 0.21/0.47    inference(forward_demodulation,[],[f80,f31])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ( ! [X18] : (k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK1,sK0))),X18)) = X18) )),
% 0.21/0.47    inference(forward_demodulation,[],[f64,f43])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X18] : (k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK1,sK0))),X18)) = k5_xboole_0(k1_xboole_0,X18)) )),
% 0.21/0.47    inference(superposition,[],[f31,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK1,sK0))))),
% 0.21/0.47    inference(backward_demodulation,[],[f38,f31])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0)))),
% 0.21/0.47    inference(backward_demodulation,[],[f33,f22])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)))),
% 0.21/0.47    inference(definition_unfolding,[],[f18,f32])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : ~(k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f12])).
% 0.21/0.47  fof(f12,conjecture,(
% 0.21/0.47    ! [X0,X1] : ~(k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    r2_xboole_0(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (24648)------------------------------
% 0.21/0.47  % (24648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (24648)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (24648)Memory used [KB]: 6268
% 0.21/0.47  % (24648)Time elapsed: 0.071 s
% 0.21/0.47  % (24648)------------------------------
% 0.21/0.47  % (24648)------------------------------
% 0.21/0.48  % (24641)Success in time 0.113 s
%------------------------------------------------------------------------------

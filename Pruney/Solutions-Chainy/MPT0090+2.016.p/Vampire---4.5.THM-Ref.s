%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 146 expanded)
%              Number of leaves         :    8 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :   75 ( 225 expanded)
%              Number of equality atoms :   50 ( 169 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    $false ),
    inference(subsumption_resolution,[],[f81,f70])).

fof(f70,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,
    ( sK0 != sK0
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f15,f67])).

fof(f67,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | sK0 = k4_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f58,f64])).

fof(f64,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3 ),
    inference(forward_demodulation,[],[f63,f17])).

fof(f17,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f63,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f51,f27])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f23,f17])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f16,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f51,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k4_xboole_0(X4,X4)) ),
    inference(superposition,[],[f26,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f22,f18])).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f58,plain,
    ( k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)
    | sK0 = k4_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f40,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f56,f17])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f47,f27])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f26,f17])).

fof(f40,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | sK0 = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f19,f35])).

fof(f35,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | sK0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f25,f14])).

fof(f14,plain,
    ( r1_xboole_0(sK0,sK1)
    | sK0 = k4_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( sK0 != k4_xboole_0(sK0,sK1)
      | ~ r1_xboole_0(sK0,sK1) )
    & ( sK0 = k4_xboole_0(sK0,sK1)
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ( k4_xboole_0(X0,X1) != X0
          | ~ r1_xboole_0(X0,X1) )
        & ( k4_xboole_0(X0,X1) = X0
          | r1_xboole_0(X0,X1) ) )
   => ( ( sK0 != k4_xboole_0(sK0,sK1)
        | ~ r1_xboole_0(sK0,sK1) )
      & ( sK0 = k4_xboole_0(sK0,sK1)
        | r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k4_xboole_0(X0,X1) != X0
        | ~ r1_xboole_0(X0,X1) )
      & ( k4_xboole_0(X0,X1) = X0
        | r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <~> k4_xboole_0(X0,X1) = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
      <=> k4_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f20,f18])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
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

fof(f15,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | sK0 != k4_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f81,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f77,f27])).

fof(f77,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | r1_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f24,f67])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f18])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:20:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (26213)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (26213)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f81,f70])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    ~r1_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f69])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    sK0 != sK0 | ~r1_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(backward_demodulation,[],[f15,f67])).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    sK0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f66])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    sK0 = k4_xboole_0(sK0,sK1) | sK0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(backward_demodulation,[],[f58,f64])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3) )),
% 0.22/0.47    inference(forward_demodulation,[],[f63,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k1_xboole_0)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f51,f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.47    inference(backward_demodulation,[],[f23,f17])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f16,f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k4_xboole_0(X4,X4))) )),
% 0.22/0.47    inference(superposition,[],[f26,f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f22,f18])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) | sK0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(backward_demodulation,[],[f40,f57])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f56,f17])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f47,f27])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0))) )),
% 0.22/0.47    inference(superposition,[],[f26,f17])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | sK0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(superposition,[],[f19,f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | sK0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(resolution,[],[f25,f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    r1_xboole_0(sK0,sK1) | sK0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    (sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1))) => ((sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1)))),
% 0.22/0.47    inference(nnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0,X1] : (r1_xboole_0(X0,X1) <~> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.47    inference(negated_conjecture,[],[f7])).
% 0.22/0.47  fof(f7,conjecture,(
% 0.22/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f20,f18])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.47    inference(nnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ~r1_xboole_0(sK0,sK1) | sK0 != k4_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    r1_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f77,f27])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    k1_xboole_0 != k4_xboole_0(sK0,sK0) | r1_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(superposition,[],[f24,f67])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f21,f18])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (26213)------------------------------
% 0.22/0.47  % (26213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (26213)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (26213)Memory used [KB]: 1663
% 0.22/0.47  % (26213)Time elapsed: 0.008 s
% 0.22/0.47  % (26213)------------------------------
% 0.22/0.47  % (26213)------------------------------
% 0.22/0.47  % (26191)Success in time 0.107 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  57 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :   13
%              Number of atoms          :   54 (  84 expanded)
%              Number of equality atoms :   30 (  45 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f135,plain,(
    $false ),
    inference(resolution,[],[f124,f15])).

fof(f15,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

fof(f124,plain,(
    ! [X3] : r1_xboole_0(sK0,k4_xboole_0(sK1,X3)) ),
    inference(trivial_inequality_removal,[],[f120])).

fof(f120,plain,(
    ! [X3] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(sK0,k4_xboole_0(sK1,X3)) ) ),
    inference(superposition,[],[f26,f101])).

fof(f101,plain,(
    ! [X13] : k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X13))) ),
    inference(forward_demodulation,[],[f100,f17])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f100,plain,(
    ! [X13] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X13))) = k4_xboole_0(k1_xboole_0,X13) ),
    inference(forward_demodulation,[],[f75,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f24,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f16,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f75,plain,(
    ! [X13] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X13))) = k4_xboole_0(k4_xboole_0(sK0,sK0),X13) ),
    inference(superposition,[],[f28,f63])).

fof(f63,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f54,f18])).

fof(f54,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f25,f39])).

fof(f39,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f27,f14])).

fof(f14,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f21,f19])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f23,f19,f19])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f19])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:10:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.41  % (10700)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.41  % (10700)Refutation found. Thanks to Tanya!
% 0.22/0.41  % SZS status Theorem for theBenchmark
% 0.22/0.41  % SZS output start Proof for theBenchmark
% 0.22/0.41  fof(f135,plain,(
% 0.22/0.41    $false),
% 0.22/0.41    inference(resolution,[],[f124,f15])).
% 0.22/0.41  fof(f15,plain,(
% 0.22/0.41    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.41    inference(cnf_transformation,[],[f12])).
% 0.22/0.41  fof(f12,plain,(
% 0.22/0.41    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1)),
% 0.22/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 0.22/0.41  fof(f11,plain,(
% 0.22/0.41    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1))),
% 0.22/0.41    introduced(choice_axiom,[])).
% 0.22/0.41  fof(f10,plain,(
% 0.22/0.41    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1))),
% 0.22/0.41    inference(ennf_transformation,[],[f9])).
% 0.22/0.41  fof(f9,negated_conjecture,(
% 0.22/0.41    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.41    inference(negated_conjecture,[],[f8])).
% 0.22/0.41  fof(f8,conjecture,(
% 0.22/0.41    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).
% 0.22/0.41  fof(f124,plain,(
% 0.22/0.41    ( ! [X3] : (r1_xboole_0(sK0,k4_xboole_0(sK1,X3))) )),
% 0.22/0.41    inference(trivial_inequality_removal,[],[f120])).
% 0.22/0.41  fof(f120,plain,(
% 0.22/0.41    ( ! [X3] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,k4_xboole_0(sK1,X3))) )),
% 0.22/0.41    inference(superposition,[],[f26,f101])).
% 0.22/0.41  fof(f101,plain,(
% 0.22/0.41    ( ! [X13] : (k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X13)))) )),
% 0.22/0.41    inference(forward_demodulation,[],[f100,f17])).
% 0.22/0.41  fof(f17,plain,(
% 0.22/0.41    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f7])).
% 0.22/0.41  fof(f7,axiom,(
% 0.22/0.41    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.41  fof(f100,plain,(
% 0.22/0.41    ( ! [X13] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X13))) = k4_xboole_0(k1_xboole_0,X13)) )),
% 0.22/0.41    inference(forward_demodulation,[],[f75,f29])).
% 0.22/0.41  fof(f29,plain,(
% 0.22/0.41    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.41    inference(backward_demodulation,[],[f24,f18])).
% 0.22/0.41  fof(f18,plain,(
% 0.22/0.41    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.41    inference(cnf_transformation,[],[f3])).
% 0.22/0.41  fof(f3,axiom,(
% 0.22/0.41    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.41  fof(f24,plain,(
% 0.22/0.41    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.41    inference(definition_unfolding,[],[f16,f19])).
% 0.22/0.41  fof(f19,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.41    inference(cnf_transformation,[],[f5])).
% 0.22/0.41  fof(f5,axiom,(
% 0.22/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.41  fof(f16,plain,(
% 0.22/0.41    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f2])).
% 0.22/0.41  fof(f2,axiom,(
% 0.22/0.41    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.41  fof(f75,plain,(
% 0.22/0.41    ( ! [X13] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X13))) = k4_xboole_0(k4_xboole_0(sK0,sK0),X13)) )),
% 0.22/0.41    inference(superposition,[],[f28,f63])).
% 0.22/0.41  fof(f63,plain,(
% 0.22/0.41    sK0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.41    inference(forward_demodulation,[],[f54,f18])).
% 0.22/0.41  fof(f54,plain,(
% 0.22/0.41    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.41    inference(superposition,[],[f25,f39])).
% 0.22/0.41  fof(f39,plain,(
% 0.22/0.41    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.22/0.41    inference(resolution,[],[f27,f14])).
% 0.22/0.41  fof(f14,plain,(
% 0.22/0.41    r1_xboole_0(sK0,sK1)),
% 0.22/0.41    inference(cnf_transformation,[],[f12])).
% 0.22/0.41  fof(f27,plain,(
% 0.22/0.41    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.41    inference(definition_unfolding,[],[f21,f19])).
% 0.22/0.41  fof(f21,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f13])).
% 0.22/0.41  fof(f13,plain,(
% 0.22/0.41    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.41    inference(nnf_transformation,[],[f1])).
% 0.22/0.41  fof(f1,axiom,(
% 0.22/0.41    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.41  fof(f25,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.41    inference(definition_unfolding,[],[f20,f19])).
% 0.22/0.41  fof(f20,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f4])).
% 0.22/0.41  fof(f4,axiom,(
% 0.22/0.41    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.41  fof(f28,plain,(
% 0.22/0.41    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.22/0.41    inference(definition_unfolding,[],[f23,f19,f19])).
% 0.22/0.41  fof(f23,plain,(
% 0.22/0.41    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f6])).
% 0.22/0.41  fof(f6,axiom,(
% 0.22/0.41    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.41  fof(f26,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.41    inference(definition_unfolding,[],[f22,f19])).
% 0.22/0.41  fof(f22,plain,(
% 0.22/0.41    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.41    inference(cnf_transformation,[],[f13])).
% 0.22/0.41  % SZS output end Proof for theBenchmark
% 0.22/0.41  % (10700)------------------------------
% 0.22/0.41  % (10700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.41  % (10700)Termination reason: Refutation
% 0.22/0.41  
% 0.22/0.41  % (10700)Memory used [KB]: 1663
% 0.22/0.41  % (10700)Time elapsed: 0.006 s
% 0.22/0.41  % (10700)------------------------------
% 0.22/0.41  % (10700)------------------------------
% 0.22/0.42  % (10686)Success in time 0.057 s
%------------------------------------------------------------------------------

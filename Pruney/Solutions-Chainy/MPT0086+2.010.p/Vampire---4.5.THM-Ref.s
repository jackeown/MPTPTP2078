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
% DateTime   : Thu Dec  3 12:31:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 161 expanded)
%              Number of leaves         :    8 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :   56 ( 207 expanded)
%              Number of equality atoms :   31 ( 150 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f832,plain,(
    $false ),
    inference(resolution,[],[f629,f36])).

fof(f36,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f33,f13])).

fof(f13,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1)
   => ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(trivial_inequality_removal,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(superposition,[],[f19,f21])).

fof(f21,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k3_xboole_0(X3,X2)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f18,f16])).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f629,plain,(
    ! [X12,X13] : r1_xboole_0(X12,k4_xboole_0(X13,X12)) ),
    inference(subsumption_resolution,[],[f496,f513])).

fof(f513,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) ),
    inference(backward_demodulation,[],[f108,f512])).

fof(f512,plain,(
    ! [X4,X3] : k1_xboole_0 = k3_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(subsumption_resolution,[],[f464,f14])).

fof(f14,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f464,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = k3_xboole_0(X3,k4_xboole_0(X4,X3))
      | ~ r1_xboole_0(k3_xboole_0(X3,X4),k1_xboole_0) ) ),
    inference(superposition,[],[f108,f21])).

fof(f108,plain,(
    ! [X2,X1] : k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(backward_demodulation,[],[f96,f103])).

fof(f103,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k3_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f20,f76])).

fof(f76,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(forward_demodulation,[],[f75,f15])).

fof(f15,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f75,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = k3_xboole_0(X1,X1) ),
    inference(subsumption_resolution,[],[f67,f14])).

fof(f67,plain,(
    ! [X1] :
      ( k4_xboole_0(X1,k1_xboole_0) = k3_xboole_0(X1,X1)
      | ~ r1_xboole_0(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f51,f18])).

fof(f51,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f17,f34])).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f17,f15])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f96,plain,(
    ! [X2,X1] : k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(backward_demodulation,[],[f54,f88])).

fof(f88,plain,(
    ! [X4,X5] : k3_xboole_0(X4,k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k3_xboole_0(X5,X4)) ),
    inference(superposition,[],[f35,f16])).

fof(f35,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f17,f17])).

fof(f54,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,X2))) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f50,f16])).

fof(f50,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,X2))) = k3_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0) ),
    inference(superposition,[],[f34,f20])).

fof(f496,plain,(
    ! [X12,X13] :
      ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,k3_xboole_0(X12,X13))
      | r1_xboole_0(X12,k4_xboole_0(X13,X12)) ) ),
    inference(superposition,[],[f19,f108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:35:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (5497)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (5497)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f832,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(resolution,[],[f629,f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 0.20/0.46    inference(resolution,[],[f33,f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),X1) => ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.46    inference(negated_conjecture,[],[f7])).
% 0.20/0.46  fof(f7,conjecture,(
% 0.20/0.46    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X0,X1) | ~r1_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(superposition,[],[f19,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(X3,X2) | ~r1_xboole_0(X2,X3)) )),
% 0.20/0.46    inference(superposition,[],[f18,f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(nnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f629,plain,(
% 0.20/0.46    ( ! [X12,X13] : (r1_xboole_0(X12,k4_xboole_0(X13,X12))) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f496,f513])).
% 0.20/0.46  fof(f513,plain,(
% 0.20/0.46    ( ! [X2,X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2))) )),
% 0.20/0.46    inference(backward_demodulation,[],[f108,f512])).
% 0.20/0.46  fof(f512,plain,(
% 0.20/0.46    ( ! [X4,X3] : (k1_xboole_0 = k3_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f464,f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.46  fof(f464,plain,(
% 0.20/0.46    ( ! [X4,X3] : (k1_xboole_0 = k3_xboole_0(X3,k4_xboole_0(X4,X3)) | ~r1_xboole_0(k3_xboole_0(X3,X4),k1_xboole_0)) )),
% 0.20/0.46    inference(superposition,[],[f108,f21])).
% 0.20/0.46  fof(f108,plain,(
% 0.20/0.46    ( ! [X2,X1] : (k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 0.20/0.46    inference(backward_demodulation,[],[f96,f103])).
% 0.20/0.46  fof(f103,plain,(
% 0.20/0.46    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k3_xboole_0(X4,k4_xboole_0(X4,X5))) )),
% 0.20/0.46    inference(superposition,[],[f20,f76])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 0.20/0.46    inference(forward_demodulation,[],[f75,f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = k3_xboole_0(X1,X1)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f67,f14])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = k3_xboole_0(X1,X1) | ~r1_xboole_0(X1,k1_xboole_0)) )),
% 0.20/0.46    inference(superposition,[],[f51,f18])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.46    inference(superposition,[],[f17,f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.20/0.46    inference(superposition,[],[f17,f15])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    ( ! [X2,X1] : (k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,k4_xboole_0(X2,X1)))) )),
% 0.20/0.46    inference(backward_demodulation,[],[f54,f88])).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    ( ! [X4,X5] : (k3_xboole_0(X4,k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k3_xboole_0(X5,X4))) )),
% 0.20/0.46    inference(superposition,[],[f35,f16])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 0.20/0.46    inference(superposition,[],[f17,f17])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,X2))) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2))) )),
% 0.20/0.46    inference(forward_demodulation,[],[f50,f16])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,X2))) = k3_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0)) )),
% 0.20/0.46    inference(superposition,[],[f34,f20])).
% 0.20/0.46  fof(f496,plain,(
% 0.20/0.46    ( ! [X12,X13] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,k3_xboole_0(X12,X13)) | r1_xboole_0(X12,k4_xboole_0(X13,X12))) )),
% 0.20/0.46    inference(superposition,[],[f19,f108])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (5497)------------------------------
% 0.20/0.46  % (5497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (5497)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (5497)Memory used [KB]: 2174
% 0.20/0.46  % (5497)Time elapsed: 0.024 s
% 0.20/0.46  % (5497)------------------------------
% 0.20/0.46  % (5497)------------------------------
% 0.20/0.46  % (5489)Success in time 0.097 s
%------------------------------------------------------------------------------

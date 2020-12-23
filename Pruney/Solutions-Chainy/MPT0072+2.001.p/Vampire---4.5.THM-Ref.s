%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   30 (  36 expanded)
%              Number of leaves         :    8 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  42 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f48])).

fof(f48,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f47,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f34,f15])).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f19,f28])).

fof(f28,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f26,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f26,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f24,f16])).

fof(f16,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f24,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f19,f16])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f47,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f46,f16])).

fof(f46,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f21,f14])).

fof(f14,plain,(
    ~ r1_xboole_0(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ~ r1_xboole_0(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f12])).

fof(f12,plain,
    ( ? [X0] : ~ r1_xboole_0(X0,k1_xboole_0)
   => ~ r1_xboole_0(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : ~ r1_xboole_0(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f20,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:56:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (14886)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (14886)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f48])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    k1_xboole_0 != k1_xboole_0),
% 0.22/0.47    inference(superposition,[],[f47,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f34,f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0)) )),
% 0.22/0.47    inference(superposition,[],[f19,f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.22/0.47    inference(superposition,[],[f26,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.22/0.47    inference(forward_demodulation,[],[f24,f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 0.22/0.47    inference(superposition,[],[f19,f16])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    k1_xboole_0 != k4_xboole_0(sK0,sK0)),
% 0.22/0.47    inference(forward_demodulation,[],[f46,f16])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0))),
% 0.22/0.47    inference(resolution,[],[f21,f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ~r1_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ~r1_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ? [X0] : ~r1_xboole_0(X0,k1_xboole_0) => ~r1_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0] : ~r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,negated_conjecture,(
% 0.22/0.47    ~! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.47    inference(negated_conjecture,[],[f7])).
% 0.22/0.47  fof(f7,conjecture,(
% 0.22/0.47    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f20,f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 => r1_xboole_0(X0,X1))),
% 0.22/0.47    inference(unused_predicate_definition_removal,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (14886)------------------------------
% 0.22/0.47  % (14886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (14886)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (14886)Memory used [KB]: 6012
% 0.22/0.47  % (14886)Time elapsed: 0.044 s
% 0.22/0.47  % (14886)------------------------------
% 0.22/0.47  % (14886)------------------------------
% 0.22/0.48  % (14883)Success in time 0.113 s
%------------------------------------------------------------------------------

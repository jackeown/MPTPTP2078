%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  74 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :   51 (  85 expanded)
%              Number of equality atoms :   37 (  71 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f391,plain,(
    $false ),
    inference(resolution,[],[f308,f19])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f308,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) ),
    inference(trivial_inequality_removal,[],[f307])).

fof(f307,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)
    | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) ),
    inference(forward_demodulation,[],[f299,f28])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f299,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) ),
    inference(superposition,[],[f42,f285])).

fof(f285,plain,(
    ! [X4,X3] :
      ( k2_xboole_0(X4,X3) = X4
      | ~ r1_tarski(X3,X4) ) ),
    inference(forward_demodulation,[],[f160,f221])).

fof(f221,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f158,f28])).

fof(f158,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(forward_demodulation,[],[f137,f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f137,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[],[f26,f17])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f20,f25])).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f160,plain,(
    ! [X4,X3] :
      ( k4_xboole_0(X4,k1_xboole_0) = k2_xboole_0(X4,X3)
      | ~ r1_tarski(X3,X4) ) ),
    inference(forward_demodulation,[],[f159,f28])).

fof(f159,plain,(
    ! [X4,X3] :
      ( k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0))) = k2_xboole_0(X4,X3)
      | ~ r1_tarski(X3,X4) ) ),
    inference(forward_demodulation,[],[f139,f18])).

fof(f139,plain,(
    ! [X4,X3] :
      ( k2_xboole_0(X4,X3) = k4_xboole_0(k2_xboole_0(X4,k1_xboole_0),k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)))
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f26,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f42,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f27,f28])).

fof(f27,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))) ),
    inference(definition_unfolding,[],[f16,f25,f21])).

fof(f16,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:21:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (14528)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.43  % (14528)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f391,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(resolution,[],[f308,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.44  fof(f308,plain,(
% 0.21/0.44    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f307])).
% 0.21/0.44  fof(f307,plain,(
% 0.21/0.44    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) | ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)),
% 0.21/0.44    inference(forward_demodulation,[],[f299,f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f22,f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.44  fof(f299,plain,(
% 0.21/0.44    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)),
% 0.21/0.44    inference(superposition,[],[f42,f285])).
% 0.21/0.44  fof(f285,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = X4 | ~r1_tarski(X3,X4)) )),
% 0.21/0.44    inference(forward_demodulation,[],[f160,f221])).
% 0.21/0.44  fof(f221,plain,(
% 0.21/0.44    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.21/0.44    inference(superposition,[],[f158,f28])).
% 0.21/0.44  fof(f158,plain,(
% 0.21/0.44    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = X0) )),
% 0.21/0.44    inference(forward_demodulation,[],[f137,f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.44  fof(f137,plain,(
% 0.21/0.44    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)))) )),
% 0.21/0.44    inference(superposition,[],[f26,f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f20,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f23,f21])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.44  fof(f160,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k4_xboole_0(X4,k1_xboole_0) = k2_xboole_0(X4,X3) | ~r1_tarski(X3,X4)) )),
% 0.21/0.44    inference(forward_demodulation,[],[f159,f28])).
% 0.21/0.44  fof(f159,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0))) = k2_xboole_0(X4,X3) | ~r1_tarski(X3,X4)) )),
% 0.21/0.44    inference(forward_demodulation,[],[f139,f18])).
% 0.21/0.44  fof(f139,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k4_xboole_0(k2_xboole_0(X4,k1_xboole_0),k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0))) | ~r1_tarski(X3,X4)) )),
% 0.21/0.44    inference(superposition,[],[f26,f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.44    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.21/0.44    inference(forward_demodulation,[],[f27,f28])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))),
% 0.21/0.44    inference(definition_unfolding,[],[f16,f25,f21])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.44    inference(negated_conjecture,[],[f9])).
% 0.21/0.44  fof(f9,conjecture,(
% 0.21/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (14528)------------------------------
% 0.21/0.44  % (14528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (14528)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (14528)Memory used [KB]: 6268
% 0.21/0.44  % (14528)Time elapsed: 0.047 s
% 0.21/0.44  % (14528)------------------------------
% 0.21/0.44  % (14528)------------------------------
% 0.21/0.44  % (14523)Success in time 0.086 s
%------------------------------------------------------------------------------

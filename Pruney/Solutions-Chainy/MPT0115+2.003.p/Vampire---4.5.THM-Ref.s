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
% DateTime   : Thu Dec  3 12:32:48 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   36 (  52 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :   49 (  81 expanded)
%              Number of equality atoms :   22 (  35 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f215,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f214])).

fof(f214,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f45,f84])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) ),
    inference(resolution,[],[f66,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f66,plain,(
    ! [X2] : r1_tarski(sK0,k2_xboole_0(sK1,X2)) ),
    inference(forward_demodulation,[],[f65,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f18,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f65,plain,(
    ! [X2] : r1_tarski(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X2))),k2_xboole_0(sK1,X2)) ),
    inference(forward_demodulation,[],[f50,f16])).

fof(f16,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f50,plain,(
    ! [X2] : r1_tarski(k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,X2))),k2_xboole_0(sK1,X2)) ),
    inference(superposition,[],[f26,f28])).

fof(f28,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f21,f14])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f23,f19,f19])).

fof(f23,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f45,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f38,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f38,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),sK1)) ),
    inference(superposition,[],[f27,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f27,plain,(
    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK1) ),
    inference(resolution,[],[f20,f24])).

fof(f24,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f15,f19])).

fof(f15,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 18:31:52 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.45  % (9019)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.23/0.46  % (9019)Refutation found. Thanks to Tanya!
% 0.23/0.46  % SZS status Theorem for theBenchmark
% 0.23/0.46  % SZS output start Proof for theBenchmark
% 0.23/0.46  fof(f215,plain,(
% 0.23/0.46    $false),
% 0.23/0.46    inference(trivial_inequality_removal,[],[f214])).
% 0.23/0.46  fof(f214,plain,(
% 0.23/0.46    k1_xboole_0 != k1_xboole_0),
% 0.23/0.46    inference(superposition,[],[f45,f84])).
% 0.23/0.46  fof(f84,plain,(
% 0.23/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,X0))) )),
% 0.23/0.46    inference(resolution,[],[f66,f21])).
% 0.23/0.46  fof(f21,plain,(
% 0.23/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.23/0.46    inference(cnf_transformation,[],[f13])).
% 0.23/0.46  fof(f13,plain,(
% 0.23/0.46    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.23/0.46    inference(nnf_transformation,[],[f2])).
% 0.23/0.46  fof(f2,axiom,(
% 0.23/0.46    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.23/0.46  fof(f66,plain,(
% 0.23/0.46    ( ! [X2] : (r1_tarski(sK0,k2_xboole_0(sK1,X2))) )),
% 0.23/0.46    inference(forward_demodulation,[],[f65,f25])).
% 0.23/0.46  fof(f25,plain,(
% 0.23/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 0.23/0.46    inference(definition_unfolding,[],[f18,f19])).
% 0.23/0.46  fof(f19,plain,(
% 0.23/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.46    inference(cnf_transformation,[],[f7])).
% 0.23/0.46  fof(f7,axiom,(
% 0.23/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.46  fof(f18,plain,(
% 0.23/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.23/0.46    inference(cnf_transformation,[],[f3])).
% 0.23/0.46  fof(f3,axiom,(
% 0.23/0.46    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.23/0.46  fof(f65,plain,(
% 0.23/0.46    ( ! [X2] : (r1_tarski(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X2))),k2_xboole_0(sK1,X2))) )),
% 0.23/0.46    inference(forward_demodulation,[],[f50,f16])).
% 0.23/0.46  fof(f16,plain,(
% 0.23/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.46    inference(cnf_transformation,[],[f5])).
% 0.23/0.46  fof(f5,axiom,(
% 0.23/0.46    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.23/0.46  fof(f50,plain,(
% 0.23/0.46    ( ! [X2] : (r1_tarski(k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,X2))),k2_xboole_0(sK1,X2))) )),
% 0.23/0.46    inference(superposition,[],[f26,f28])).
% 0.23/0.46  fof(f28,plain,(
% 0.23/0.46    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.23/0.46    inference(resolution,[],[f21,f14])).
% 0.23/0.46  fof(f14,plain,(
% 0.23/0.46    r1_tarski(sK0,sK1)),
% 0.23/0.46    inference(cnf_transformation,[],[f12])).
% 0.23/0.46  fof(f12,plain,(
% 0.23/0.46    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1)),
% 0.23/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 0.23/0.46  fof(f11,plain,(
% 0.23/0.46    ? [X0,X1,X2] : (~r1_tarski(k3_xboole_0(X0,X2),X1) & r1_tarski(X0,X1)) => (~r1_tarski(k3_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1))),
% 0.23/0.46    introduced(choice_axiom,[])).
% 0.23/0.46  fof(f10,plain,(
% 0.23/0.46    ? [X0,X1,X2] : (~r1_tarski(k3_xboole_0(X0,X2),X1) & r1_tarski(X0,X1))),
% 0.23/0.46    inference(ennf_transformation,[],[f9])).
% 0.23/0.46  fof(f9,negated_conjecture,(
% 0.23/0.46    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.23/0.46    inference(negated_conjecture,[],[f8])).
% 0.23/0.46  fof(f8,conjecture,(
% 0.23/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.23/0.46  fof(f26,plain,(
% 0.23/0.46    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2))) )),
% 0.23/0.46    inference(definition_unfolding,[],[f23,f19,f19])).
% 0.23/0.46  fof(f23,plain,(
% 0.23/0.46    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.23/0.46    inference(cnf_transformation,[],[f4])).
% 0.23/0.46  fof(f4,axiom,(
% 0.23/0.46    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.23/0.46  fof(f45,plain,(
% 0.23/0.46    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2)))),
% 0.23/0.46    inference(forward_demodulation,[],[f38,f17])).
% 0.23/0.46  fof(f17,plain,(
% 0.23/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.23/0.46    inference(cnf_transformation,[],[f1])).
% 0.23/0.46  fof(f1,axiom,(
% 0.23/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.23/0.46  fof(f38,plain,(
% 0.23/0.46    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),sK1))),
% 0.23/0.46    inference(superposition,[],[f27,f22])).
% 0.23/0.46  fof(f22,plain,(
% 0.23/0.46    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.23/0.46    inference(cnf_transformation,[],[f6])).
% 0.23/0.46  fof(f6,axiom,(
% 0.23/0.46    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.23/0.46  fof(f27,plain,(
% 0.23/0.46    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK1)),
% 0.23/0.46    inference(resolution,[],[f20,f24])).
% 0.23/0.46  fof(f24,plain,(
% 0.23/0.46    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK1)),
% 0.23/0.46    inference(definition_unfolding,[],[f15,f19])).
% 0.23/0.46  fof(f15,plain,(
% 0.23/0.46    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1)),
% 0.23/0.46    inference(cnf_transformation,[],[f12])).
% 0.23/0.46  fof(f20,plain,(
% 0.23/0.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.23/0.46    inference(cnf_transformation,[],[f13])).
% 0.23/0.46  % SZS output end Proof for theBenchmark
% 0.23/0.46  % (9019)------------------------------
% 0.23/0.46  % (9019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.46  % (9019)Termination reason: Refutation
% 0.23/0.46  
% 0.23/0.46  % (9019)Memory used [KB]: 1791
% 0.23/0.46  % (9019)Time elapsed: 0.036 s
% 0.23/0.46  % (9019)------------------------------
% 0.23/0.46  % (9019)------------------------------
% 0.23/0.46  % (9017)Success in time 0.09 s
%------------------------------------------------------------------------------

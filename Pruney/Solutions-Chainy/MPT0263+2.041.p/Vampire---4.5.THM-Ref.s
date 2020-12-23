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
% DateTime   : Thu Dec  3 12:40:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  78 expanded)
%              Number of leaves         :    9 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :   62 ( 110 expanded)
%              Number of equality atoms :   38 (  80 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(resolution,[],[f89,f29])).

fof(f29,plain,(
    ~ r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f16,f27])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f20])).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f16,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    & ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
      & ~ r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f89,plain,(
    r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(trivial_inequality_removal,[],[f82])).

fof(f82,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0)
    | r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(superposition,[],[f24,f75])).

fof(f75,plain,(
    k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0)
    | k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(superposition,[],[f41,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_enumset1(X0,X0,X0)))
      | k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),X1) ) ),
    inference(resolution,[],[f31,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f26,f27,f27])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_enumset1(X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) ) ),
    inference(definition_unfolding,[],[f22,f27,f21,f27])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f41,plain,(
    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) ),
    inference(superposition,[],[f28,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f21,f21])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f28,plain,(
    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f17,f27,f21,f27])).

fof(f17,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:44:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (9656)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.43  % (9656)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(resolution,[],[f89,f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ~r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),
% 0.21/0.43    inference(definition_unfolding,[],[f16,f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f18,f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.43    inference(negated_conjecture,[],[f8])).
% 0.21/0.43  fof(f8,conjecture,(
% 0.21/0.43    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f82])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0) | r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),
% 0.21/0.43    inference(superposition,[],[f24,f75])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f74])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0) | k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),
% 0.21/0.43    inference(superposition,[],[f41,f48])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) | k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),X1)) )),
% 0.21/0.43    inference(resolution,[],[f31,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),X1)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f26,f27,f27])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.21/0.43    inference(nnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_enumset1(X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_enumset1(X0,X0,X0)))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f22,f27,f21,f27])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))),
% 0.21/0.43    inference(superposition,[],[f28,f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f19,f21,f21])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))),
% 0.21/0.43    inference(definition_unfolding,[],[f17,f27,f21,f27])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(nnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (9656)------------------------------
% 0.21/0.43  % (9656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (9656)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (9656)Memory used [KB]: 1663
% 0.21/0.43  % (9656)Time elapsed: 0.006 s
% 0.21/0.43  % (9656)------------------------------
% 0.21/0.43  % (9656)------------------------------
% 0.21/0.43  % (9654)Success in time 0.072 s
%------------------------------------------------------------------------------

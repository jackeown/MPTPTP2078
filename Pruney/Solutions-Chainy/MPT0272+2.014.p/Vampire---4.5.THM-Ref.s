%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  96 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   80 ( 134 expanded)
%              Number of equality atoms :   49 ( 103 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(subsumption_resolution,[],[f54,f41])).

fof(f41,plain,(
    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f36,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f36,plain,(
    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f22,f27,f34])).

fof(f34,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f22,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
        & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f54,plain,(
    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(trivial_inequality_removal,[],[f51])).

fof(f51,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f42,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))
      | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ) ),
    inference(superposition,[],[f45,f25])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))
      | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) ) ),
    inference(resolution,[],[f43,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) ) ),
    inference(resolution,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f31,f27])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) ) ),
    inference(resolution,[],[f38,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f34])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f42,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f35,f25])).

fof(f35,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f23,f34,f27,f34])).

fof(f23,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:25:55 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.40  % (2257)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.40  % (2257)Refutation found. Thanks to Tanya!
% 0.20/0.40  % SZS status Theorem for theBenchmark
% 0.20/0.40  % SZS output start Proof for theBenchmark
% 0.20/0.40  fof(f55,plain,(
% 0.20/0.40    $false),
% 0.20/0.40    inference(subsumption_resolution,[],[f54,f41])).
% 0.20/0.40  fof(f41,plain,(
% 0.20/0.40    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.20/0.40    inference(backward_demodulation,[],[f36,f25])).
% 0.20/0.40  fof(f25,plain,(
% 0.20/0.40    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f1])).
% 0.20/0.40  fof(f1,axiom,(
% 0.20/0.40    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.40  fof(f36,plain,(
% 0.20/0.40    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 0.20/0.40    inference(definition_unfolding,[],[f22,f27,f34])).
% 0.20/0.40  fof(f34,plain,(
% 0.20/0.40    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.40    inference(definition_unfolding,[],[f24,f33])).
% 0.20/0.40  fof(f33,plain,(
% 0.20/0.40    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.40    inference(definition_unfolding,[],[f26,f32])).
% 0.20/0.40  fof(f32,plain,(
% 0.20/0.40    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f7])).
% 0.20/0.40  fof(f7,axiom,(
% 0.20/0.40    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.40  fof(f26,plain,(
% 0.20/0.40    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f6])).
% 0.20/0.40  fof(f6,axiom,(
% 0.20/0.40    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.40  fof(f24,plain,(
% 0.20/0.40    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f5])).
% 0.20/0.40  fof(f5,axiom,(
% 0.20/0.40    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.40  fof(f27,plain,(
% 0.20/0.40    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.40    inference(cnf_transformation,[],[f3])).
% 0.20/0.40  fof(f3,axiom,(
% 0.20/0.40    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.40  fof(f22,plain,(
% 0.20/0.40    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.40    inference(cnf_transformation,[],[f21])).
% 0.20/0.40  fof(f21,plain,(
% 0.20/0.40    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f20])).
% 0.20/0.40  fof(f20,plain,(
% 0.20/0.40    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1))),
% 0.20/0.40    introduced(choice_axiom,[])).
% 0.20/0.40  fof(f15,plain,(
% 0.20/0.40    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.40    inference(ennf_transformation,[],[f11])).
% 0.20/0.40  fof(f11,negated_conjecture,(
% 0.20/0.40    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.40    inference(negated_conjecture,[],[f10])).
% 0.20/0.40  fof(f10,conjecture,(
% 0.20/0.40    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 0.20/0.40  fof(f54,plain,(
% 0.20/0.40    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.20/0.40    inference(trivial_inequality_removal,[],[f51])).
% 0.20/0.40  fof(f51,plain,(
% 0.20/0.40    k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.20/0.40    inference(superposition,[],[f42,f46])).
% 0.20/0.40  fof(f46,plain,(
% 0.20/0.40    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) )),
% 0.20/0.40    inference(superposition,[],[f45,f25])).
% 0.20/0.40  fof(f45,plain,(
% 0.20/0.40    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))) )),
% 0.20/0.40    inference(resolution,[],[f43,f44])).
% 0.20/0.40  fof(f44,plain,(
% 0.20/0.40    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))) )),
% 0.20/0.40    inference(resolution,[],[f40,f39])).
% 0.20/0.40  fof(f39,plain,(
% 0.20/0.40    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.40    inference(definition_unfolding,[],[f30,f34])).
% 0.20/0.40  fof(f30,plain,(
% 0.20/0.40    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f18])).
% 0.20/0.40  fof(f18,plain,(
% 0.20/0.40    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 0.20/0.40    inference(ennf_transformation,[],[f12])).
% 0.20/0.40  fof(f12,plain,(
% 0.20/0.40    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 0.20/0.40    inference(unused_predicate_definition_removal,[],[f8])).
% 0.20/0.40  fof(f8,axiom,(
% 0.20/0.40    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.40  fof(f40,plain,(
% 0.20/0.40    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.40    inference(definition_unfolding,[],[f31,f27])).
% 0.20/0.40  fof(f31,plain,(
% 0.20/0.40    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f19])).
% 0.20/0.40  fof(f19,plain,(
% 0.20/0.40    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.20/0.40    inference(ennf_transformation,[],[f13])).
% 0.20/0.40  fof(f13,plain,(
% 0.20/0.40    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.40    inference(unused_predicate_definition_removal,[],[f2])).
% 0.20/0.40  fof(f2,axiom,(
% 0.20/0.40    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.40  fof(f43,plain,(
% 0.20/0.40    ( ! [X0,X1] : (r2_hidden(X0,X1) | k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))) )),
% 0.20/0.40    inference(resolution,[],[f38,f37])).
% 0.20/0.40  fof(f37,plain,(
% 0.20/0.40    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.40    inference(definition_unfolding,[],[f28,f34])).
% 0.20/0.40  fof(f28,plain,(
% 0.20/0.40    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f16])).
% 0.20/0.40  fof(f16,plain,(
% 0.20/0.40    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.40    inference(ennf_transformation,[],[f9])).
% 0.20/0.40  fof(f9,axiom,(
% 0.20/0.40    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.20/0.40  fof(f38,plain,(
% 0.20/0.40    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.20/0.40    inference(definition_unfolding,[],[f29,f27])).
% 0.20/0.40  fof(f29,plain,(
% 0.20/0.40    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f17])).
% 0.20/0.40  fof(f17,plain,(
% 0.20/0.40    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.40    inference(ennf_transformation,[],[f14])).
% 0.20/0.40  fof(f14,plain,(
% 0.20/0.40    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 0.20/0.40    inference(unused_predicate_definition_removal,[],[f4])).
% 0.20/0.40  fof(f4,axiom,(
% 0.20/0.40    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.40  fof(f42,plain,(
% 0.20/0.40    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.20/0.40    inference(backward_demodulation,[],[f35,f25])).
% 0.20/0.40  fof(f35,plain,(
% 0.20/0.40    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 0.20/0.40    inference(definition_unfolding,[],[f23,f34,f27,f34])).
% 0.20/0.40  fof(f23,plain,(
% 0.20/0.40    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.40    inference(cnf_transformation,[],[f21])).
% 0.20/0.40  % SZS output end Proof for theBenchmark
% 0.20/0.40  % (2257)------------------------------
% 0.20/0.40  % (2257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.40  % (2257)Termination reason: Refutation
% 0.20/0.40  
% 0.20/0.40  % (2257)Memory used [KB]: 6140
% 0.20/0.40  % (2257)Time elapsed: 0.006 s
% 0.20/0.40  % (2257)------------------------------
% 0.20/0.40  % (2257)------------------------------
% 0.20/0.41  % (2241)Success in time 0.064 s
%------------------------------------------------------------------------------

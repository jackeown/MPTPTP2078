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
% DateTime   : Thu Dec  3 12:43:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  86 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 ( 119 expanded)
%              Number of equality atoms :   49 ( 108 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(subsumption_resolution,[],[f48,f18])).

fof(f18,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0))
        & X0 != X1 )
   => ( k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( X0 != X1
       => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( X0 != X1
     => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_zfmisc_1)).

fof(f48,plain,(
    sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f45])).

fof(f45,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(sK1,sK1,sK1)) != k4_xboole_0(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(sK1,sK1,sK1))
    | sK0 = sK1 ),
    inference(superposition,[],[f30,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(k4_xboole_0(X0,k1_enumset1(X1,X1,X1)),k4_xboole_0(X0,k1_enumset1(X1,X1,X1)),k1_enumset1(X2,X2,X2))) = k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X2,X2,X2))),k1_enumset1(X1,X1,X1))
      | X1 = X2 ) ),
    inference(resolution,[],[f31,f38])).

fof(f38,plain,(
    ! [X2,X1] :
      ( r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2))
      | X1 = X2 ) ),
    inference(trivial_inequality_removal,[],[f37])).

fof(f37,plain,(
    ! [X2,X1] :
      ( k1_enumset1(X1,X1,X1) != k1_enumset1(X1,X1,X1)
      | r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2))
      | X1 = X2 ) ),
    inference(superposition,[],[f23,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f22,f29,f29,f29])).

fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_tarski(k1_enumset1(k4_xboole_0(X2,X0),k4_xboole_0(X2,X0),X1)) = k4_xboole_0(k3_tarski(k1_enumset1(X2,X2,X1)),X0) ) ),
    inference(definition_unfolding,[],[f20,f28,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

fof(f30,plain,(
    k4_xboole_0(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(sK1,sK1,sK1)) != k3_tarski(k1_enumset1(k4_xboole_0(sK2,k1_enumset1(sK1,sK1,sK1)),k4_xboole_0(sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f19,f28,f29,f29,f28,f29,f29])).

fof(f19,plain,(
    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:43:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (10117)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (10120)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (10117)Refutation not found, incomplete strategy% (10117)------------------------------
% 0.21/0.52  % (10117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10117)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10117)Memory used [KB]: 10618
% 0.21/0.52  % (10117)Time elapsed: 0.107 s
% 0.21/0.52  % (10117)------------------------------
% 0.21/0.52  % (10117)------------------------------
% 0.21/0.52  % (10120)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f48,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    sK0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) & sK0 != sK1),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) & X0 != X1) => (k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) & sK0 != sK1)),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) & X0 != X1)),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f9])).
% 0.21/0.52  fof(f9,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_zfmisc_1)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    sK0 = sK1),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    k4_xboole_0(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(sK1,sK1,sK1)) != k4_xboole_0(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(sK1,sK1,sK1)) | sK0 = sK1),
% 0.21/0.52    inference(superposition,[],[f30,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(k4_xboole_0(X0,k1_enumset1(X1,X1,X1)),k4_xboole_0(X0,k1_enumset1(X1,X1,X1)),k1_enumset1(X2,X2,X2))) = k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X2,X2,X2))),k1_enumset1(X1,X1,X1)) | X1 = X2) )),
% 0.21/0.52    inference(resolution,[],[f31,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X2,X1] : (r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)) | X1 = X2) )),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k1_enumset1(X1,X1,X1) != k1_enumset1(X1,X1,X1) | r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)) | X1 = X2) )),
% 0.21/0.52    inference(superposition,[],[f23,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) | X0 = X1) )),
% 0.21/0.52    inference(definition_unfolding,[],[f22,f29,f29,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f25,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 0.21/0.52    inference(unused_predicate_definition_removal,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_tarski(k1_enumset1(k4_xboole_0(X2,X0),k4_xboole_0(X2,X0),X1)) = k4_xboole_0(k3_tarski(k1_enumset1(X2,X2,X1)),X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f20,f28,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f27,f26])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    k4_xboole_0(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(sK1,sK1,sK1)) != k3_tarski(k1_enumset1(k4_xboole_0(sK2,k1_enumset1(sK1,sK1,sK1)),k4_xboole_0(sK2,k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK0,sK0,sK0)))),
% 0.21/0.52    inference(definition_unfolding,[],[f19,f28,f29,f29,f28,f29,f29])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (10120)------------------------------
% 0.21/0.52  % (10120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10120)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (10120)Memory used [KB]: 6268
% 0.21/0.52  % (10120)Time elapsed: 0.110 s
% 0.21/0.52  % (10120)------------------------------
% 0.21/0.52  % (10120)------------------------------
% 0.21/0.52  % (10121)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (10139)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (10131)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (10127)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (10131)Refutation not found, incomplete strategy% (10131)------------------------------
% 0.21/0.52  % (10131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10131)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10131)Memory used [KB]: 6140
% 0.21/0.52  % (10131)Time elapsed: 0.078 s
% 0.21/0.52  % (10131)------------------------------
% 0.21/0.52  % (10131)------------------------------
% 0.21/0.53  % (10114)Success in time 0.162 s
%------------------------------------------------------------------------------

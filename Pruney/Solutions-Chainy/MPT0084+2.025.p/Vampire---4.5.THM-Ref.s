%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 105 expanded)
%              Number of leaves         :    8 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :   88 ( 191 expanded)
%              Number of equality atoms :   20 (  73 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f233,plain,(
    $false ),
    inference(subsumption_resolution,[],[f232,f76])).

fof(f76,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f50,f17])).

fof(f17,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f50,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X2,X3)
      | k1_xboole_0 != k4_xboole_0(X3,k4_xboole_0(X3,X2)) ) ),
    inference(superposition,[],[f29,f28])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f21,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f232,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f231,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f231,plain,(
    r1_xboole_0(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f230])).

fof(f230,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f223,f34])).

fof(f34,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f30,f27])).

fof(f27,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f19,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f223,plain,(
    ! [X0] :
      ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK2))))
      | r1_xboole_0(X0,sK0) ) ),
    inference(superposition,[],[f214,f28])).

% (11253)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f214,plain,(
    ! [X0] :
      ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))))
      | r1_xboole_0(X0,sK0) ) ),
    inference(resolution,[],[f158,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f21])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f158,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),X1)
      | k1_xboole_0 != k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) ) ),
    inference(resolution,[],[f123,f50])).

fof(f123,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X2)),X3)
      | r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,sK0)),X3) ) ),
    inference(resolution,[],[f114,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f114,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) ),
    inference(superposition,[],[f107,f28])).

fof(f107,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) ),
    inference(resolution,[],[f32,f18])).

fof(f18,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f25,f21,f21])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:47:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (11254)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (11241)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (11245)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (11255)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (11254)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f232,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 0.21/0.48    inference(resolution,[],[f50,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X2,X3] : (r1_xboole_0(X2,X3) | k1_xboole_0 != k4_xboole_0(X3,k4_xboole_0(X3,X2))) )),
% 0.21/0.48    inference(superposition,[],[f29,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f20,f21,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f23,f21])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 0.21/0.48    inference(resolution,[],[f231,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f22,f21])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    r1_xboole_0(sK1,sK0)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f230])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,sK0)),
% 0.21/0.48    inference(superposition,[],[f223,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 0.21/0.48    inference(resolution,[],[f30,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.21/0.48    inference(definition_unfolding,[],[f19,f21])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK2)))) | r1_xboole_0(X0,sK0)) )),
% 0.21/0.48    inference(superposition,[],[f214,f28])).
% 0.21/0.48  % (11253)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  fof(f214,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) | r1_xboole_0(X0,sK0)) )),
% 0.21/0.48    inference(resolution,[],[f158,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f24,f21])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),X1) | k1_xboole_0 != k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))))) )),
% 0.21/0.48    inference(resolution,[],[f123,f50])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X2)),X3) | r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,sK0)),X3)) )),
% 0.21/0.48    inference(resolution,[],[f114,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) )),
% 0.21/0.48    inference(superposition,[],[f107,f28])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) )),
% 0.21/0.48    inference(resolution,[],[f32,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    r1_tarski(sK0,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f25,f21,f21])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (11254)------------------------------
% 0.21/0.48  % (11254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11254)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (11254)Memory used [KB]: 6268
% 0.21/0.49  % (11254)Time elapsed: 0.061 s
% 0.21/0.49  % (11254)------------------------------
% 0.21/0.49  % (11254)------------------------------
% 0.21/0.49  % (11239)Success in time 0.126 s
%------------------------------------------------------------------------------

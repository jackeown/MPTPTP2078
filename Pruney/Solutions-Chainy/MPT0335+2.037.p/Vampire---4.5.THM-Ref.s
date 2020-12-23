%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  83 expanded)
%              Number of leaves         :    8 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :   69 ( 204 expanded)
%              Number of equality atoms :   37 ( 113 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f66])).

fof(f66,plain,(
    k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f30,f57])).

fof(f57,plain,(
    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f35,f41])).

fof(f41,plain,(
    ! [X6] : k3_xboole_0(sK0,k3_xboole_0(sK1,X6)) = k3_xboole_0(sK0,X6) ),
    inference(superposition,[],[f25,f31])).

fof(f31,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f23,f16])).

fof(f16,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
    & r2_hidden(sK3,sK0)
    & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f14])).

% (29923)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f14,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_tarski(X3) != k3_xboole_0(X0,X2)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
      & r2_hidden(sK3,sK0)
      & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f35,plain,(
    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f34,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f34,plain,(
    k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
    inference(resolution,[],[f33,f23])).

fof(f33,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f32,f28])).

% (29921)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f28,plain,(
    k3_xboole_0(sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f17,f26])).

fof(f26,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f17,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),sK0) ),
    inference(resolution,[],[f29,f18])).

fof(f18,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f24,f26])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f30,plain,(
    k3_xboole_0(sK0,sK2) != k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f27,f28])).

fof(f27,plain,(
    k3_xboole_0(sK0,sK2) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f19,f26])).

fof(f19,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:31:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (29918)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (29924)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (29919)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (29922)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (29918)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,sK2)),
% 0.21/0.51    inference(superposition,[],[f30,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK1,sK2)),
% 0.21/0.51    inference(backward_demodulation,[],[f35,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X6] : (k3_xboole_0(sK0,k3_xboole_0(sK1,X6)) = k3_xboole_0(sK0,X6)) )),
% 0.21/0.51    inference(superposition,[],[f25,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    sK0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.51    inference(resolution,[],[f23,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    r1_tarski(sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f14])).
% 0.21/0.51  % (29923)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 0.21/0.51    inference(negated_conjecture,[],[f7])).
% 0.21/0.51  fof(f7,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.51    inference(superposition,[],[f34,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)),
% 0.21/0.51    inference(resolution,[],[f33,f23])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    r1_tarski(k3_xboole_0(sK1,sK2),sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f32,f28])).
% 0.21/0.51  % (29921)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    k3_xboole_0(sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK3)),
% 0.21/0.51    inference(definition_unfolding,[],[f17,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f20,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    k1_tarski(sK3) = k3_xboole_0(sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),sK0)),
% 0.21/0.51    inference(resolution,[],[f29,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    r2_hidden(sK3,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f24,f26])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 0.21/0.51    inference(unused_predicate_definition_removal,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    k3_xboole_0(sK0,sK2) != k3_xboole_0(sK1,sK2)),
% 0.21/0.51    inference(superposition,[],[f27,f28])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    k3_xboole_0(sK0,sK2) != k2_enumset1(sK3,sK3,sK3,sK3)),
% 0.21/0.51    inference(definition_unfolding,[],[f19,f26])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (29918)------------------------------
% 0.21/0.51  % (29918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29918)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (29918)Memory used [KB]: 6140
% 0.21/0.51  % (29918)Time elapsed: 0.064 s
% 0.21/0.51  % (29918)------------------------------
% 0.21/0.51  % (29918)------------------------------
% 0.21/0.51  % (29915)Success in time 0.143 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:48 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :    9 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 (  66 expanded)
%              Number of equality atoms :   27 (  35 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f206,plain,(
    $false ),
    inference(subsumption_resolution,[],[f205,f25])).

fof(f25,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f205,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f204,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f204,plain,(
    ~ r1_tarski(k1_tarski(sK0),sK1) ),
    inference(trivial_inequality_removal,[],[f201])).

fof(f201,plain,
    ( sK1 != sK1
    | ~ r1_tarski(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f26,f101])).

fof(f101,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(backward_demodulation,[],[f79,f100])).

fof(f100,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f82,f43])).

fof(f43,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f31,f28])).

fof(f28,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f82,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f38,f27])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f79,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X2,X3) = k5_xboole_0(X2,k5_xboole_0(X2,X3))
      | ~ r1_tarski(X2,X3) ) ),
    inference(forward_demodulation,[],[f69,f31])).

fof(f69,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X2,X3) = k5_xboole_0(k5_xboole_0(X2,X3),X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f34,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f26,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.45  % (28926)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.46  % (28922)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.46  % (28935)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.46  % (28928)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.46  % (28924)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.47  % (28933)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.47  % (28930)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.47  % (28920)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.47  % (28919)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.47  % (28921)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.48  % (28925)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.48  % (28927)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.48  % (28918)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.48  % (28921)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f206,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(subsumption_resolution,[],[f205,f25])).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    r2_hidden(sK0,sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 0.19/0.48    inference(ennf_transformation,[],[f18])).
% 0.19/0.48  fof(f18,negated_conjecture,(
% 0.19/0.48    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.19/0.48    inference(negated_conjecture,[],[f17])).
% 0.19/0.48  fof(f17,conjecture,(
% 0.19/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 0.19/0.48  fof(f205,plain,(
% 0.19/0.48    ~r2_hidden(sK0,sK1)),
% 0.19/0.48    inference(resolution,[],[f204,f36])).
% 0.19/0.48  fof(f36,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f22])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 0.19/0.48    inference(ennf_transformation,[],[f19])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 0.19/0.48    inference(unused_predicate_definition_removal,[],[f15])).
% 0.19/0.48  fof(f15,axiom,(
% 0.19/0.48    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.19/0.48  fof(f204,plain,(
% 0.19/0.48    ~r1_tarski(k1_tarski(sK0),sK1)),
% 0.19/0.48    inference(trivial_inequality_removal,[],[f201])).
% 0.19/0.48  fof(f201,plain,(
% 0.19/0.48    sK1 != sK1 | ~r1_tarski(k1_tarski(sK0),sK1)),
% 0.19/0.48    inference(superposition,[],[f26,f101])).
% 0.19/0.48  fof(f101,plain,(
% 0.19/0.48    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = X3 | ~r1_tarski(X2,X3)) )),
% 0.19/0.48    inference(backward_demodulation,[],[f79,f100])).
% 0.19/0.48  fof(f100,plain,(
% 0.19/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.19/0.48    inference(forward_demodulation,[],[f82,f43])).
% 0.19/0.48  fof(f43,plain,(
% 0.19/0.48    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.19/0.48    inference(superposition,[],[f31,f28])).
% 0.19/0.48  fof(f28,plain,(
% 0.19/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.48    inference(cnf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.19/0.48  fof(f31,plain,(
% 0.19/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.19/0.48  fof(f82,plain,(
% 0.19/0.48    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.19/0.48    inference(superposition,[],[f38,f27])).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,axiom,(
% 0.19/0.48    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.19/0.48  fof(f38,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f5])).
% 0.19/0.48  fof(f5,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.19/0.48  fof(f79,plain,(
% 0.19/0.48    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(X2,k5_xboole_0(X2,X3)) | ~r1_tarski(X2,X3)) )),
% 0.19/0.48    inference(forward_demodulation,[],[f69,f31])).
% 0.19/0.48  fof(f69,plain,(
% 0.19/0.48    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(k5_xboole_0(X2,X3),X2) | ~r1_tarski(X2,X3)) )),
% 0.19/0.48    inference(superposition,[],[f34,f35])).
% 0.19/0.48  fof(f35,plain,(
% 0.19/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f21])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.48    inference(ennf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f7])).
% 0.19/0.48  fof(f7,axiom,(
% 0.19/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.19/0.48  fof(f26,plain,(
% 0.19/0.48    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f24])).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (28921)------------------------------
% 0.19/0.48  % (28921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (28921)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (28921)Memory used [KB]: 1791
% 0.19/0.48  % (28921)Time elapsed: 0.077 s
% 0.19/0.48  % (28921)------------------------------
% 0.19/0.48  % (28921)------------------------------
% 0.19/0.48  % (28917)Success in time 0.131 s
%------------------------------------------------------------------------------

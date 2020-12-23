%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:52 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   30 (  39 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :   11
%              Number of atoms          :   48 (  64 expanded)
%              Number of equality atoms :   23 (  33 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(subsumption_resolution,[],[f72,f20])).

fof(f20,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f72,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f70,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f70,plain,(
    ~ r1_tarski(k1_tarski(sK0),sK1) ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,
    ( sK1 != sK1
    | ~ r1_tarski(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f54,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f47,f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = k2_xboole_0(X1,k1_xboole_0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f28,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f54,plain,(
    sK1 != k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f50,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f50,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f34,f28])).

fof(f34,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(superposition,[],[f21,f24])).

fof(f21,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:06:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.44  % (616)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.18/0.45  % (613)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.18/0.45  % (613)Refutation found. Thanks to Tanya!
% 0.18/0.45  % SZS status Theorem for theBenchmark
% 0.18/0.45  % (615)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.18/0.45  % (610)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.18/0.45  % (614)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.18/0.46  % (623)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.18/0.46  % (620)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.18/0.46  % (622)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.18/0.46  % SZS output start Proof for theBenchmark
% 0.18/0.46  fof(f73,plain,(
% 0.18/0.46    $false),
% 0.18/0.46    inference(subsumption_resolution,[],[f72,f20])).
% 0.18/0.46  fof(f20,plain,(
% 0.18/0.46    r2_hidden(sK0,sK1)),
% 0.18/0.46    inference(cnf_transformation,[],[f19])).
% 0.18/0.46  fof(f19,plain,(
% 0.18/0.46    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 0.18/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18])).
% 0.18/0.46  fof(f18,plain,(
% 0.18/0.46    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 0.18/0.46    introduced(choice_axiom,[])).
% 0.18/0.46  fof(f15,plain,(
% 0.18/0.46    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 0.18/0.46    inference(ennf_transformation,[],[f12])).
% 0.18/0.46  fof(f12,negated_conjecture,(
% 0.18/0.46    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.18/0.46    inference(negated_conjecture,[],[f11])).
% 0.18/0.46  fof(f11,conjecture,(
% 0.18/0.46    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 0.18/0.46  fof(f72,plain,(
% 0.18/0.46    ~r2_hidden(sK0,sK1)),
% 0.18/0.46    inference(resolution,[],[f70,f29])).
% 0.18/0.46  fof(f29,plain,(
% 0.18/0.46    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f16])).
% 0.18/0.46  fof(f16,plain,(
% 0.18/0.46    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 0.18/0.46    inference(ennf_transformation,[],[f13])).
% 0.18/0.46  fof(f13,plain,(
% 0.18/0.46    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 0.18/0.46    inference(unused_predicate_definition_removal,[],[f9])).
% 0.18/0.46  fof(f9,axiom,(
% 0.18/0.46    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.18/0.46  fof(f70,plain,(
% 0.18/0.46    ~r1_tarski(k1_tarski(sK0),sK1)),
% 0.18/0.46    inference(trivial_inequality_removal,[],[f69])).
% 0.18/0.46  fof(f69,plain,(
% 0.18/0.46    sK1 != sK1 | ~r1_tarski(k1_tarski(sK0),sK1)),
% 0.18/0.46    inference(superposition,[],[f54,f51])).
% 0.18/0.46  fof(f51,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = X1 | ~r1_tarski(X0,X1)) )),
% 0.18/0.46    inference(forward_demodulation,[],[f47,f22])).
% 0.18/0.46  fof(f22,plain,(
% 0.18/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.18/0.46    inference(cnf_transformation,[],[f4])).
% 0.18/0.46  fof(f4,axiom,(
% 0.18/0.46    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.18/0.46  fof(f47,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X0,X1)) )),
% 0.18/0.46    inference(superposition,[],[f28,f30])).
% 0.18/0.46  fof(f30,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f17])).
% 0.18/0.46  fof(f17,plain,(
% 0.18/0.46    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.18/0.46    inference(ennf_transformation,[],[f14])).
% 0.18/0.46  fof(f14,plain,(
% 0.18/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 0.18/0.46    inference(unused_predicate_definition_removal,[],[f2])).
% 0.18/0.46  fof(f2,axiom,(
% 0.18/0.46    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.18/0.46  fof(f28,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.18/0.46    inference(cnf_transformation,[],[f5])).
% 0.18/0.46  fof(f5,axiom,(
% 0.18/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.18/0.46  fof(f54,plain,(
% 0.18/0.46    sK1 != k2_xboole_0(sK1,k1_tarski(sK0))),
% 0.18/0.46    inference(superposition,[],[f50,f24])).
% 0.18/0.46  fof(f24,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f1])).
% 0.18/0.46  fof(f1,axiom,(
% 0.18/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.18/0.46  fof(f50,plain,(
% 0.18/0.46    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.18/0.46    inference(superposition,[],[f34,f28])).
% 0.18/0.46  fof(f34,plain,(
% 0.18/0.46    sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))),
% 0.18/0.46    inference(superposition,[],[f21,f24])).
% 0.18/0.46  fof(f21,plain,(
% 0.18/0.46    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.18/0.46    inference(cnf_transformation,[],[f19])).
% 0.18/0.46  % SZS output end Proof for theBenchmark
% 0.18/0.46  % (613)------------------------------
% 0.18/0.46  % (613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (613)Termination reason: Refutation
% 0.18/0.46  
% 0.18/0.46  % (613)Memory used [KB]: 1663
% 0.18/0.46  % (613)Time elapsed: 0.054 s
% 0.18/0.46  % (613)------------------------------
% 0.18/0.46  % (613)------------------------------
% 0.18/0.46  % (621)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.18/0.46  % (609)Success in time 0.119 s
%------------------------------------------------------------------------------

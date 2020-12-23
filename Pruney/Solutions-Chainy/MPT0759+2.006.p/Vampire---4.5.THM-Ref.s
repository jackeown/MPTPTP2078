%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  29 expanded)
%              Number of leaves         :    8 (   9 expanded)
%              Depth                    :    9
%              Number of atoms          :   36 (  38 expanded)
%              Number of equality atoms :   29 (  31 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28,f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) != X0 ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f16,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f15,plain,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

fof(f28,plain,(
    sK0 = k2_xboole_0(sK0,k1_tarski(sK0)) ),
    inference(superposition,[],[f27,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f27,plain,(
    sK0 = k2_xboole_0(k1_tarski(sK0),sK0) ),
    inference(trivial_inequality_removal,[],[f26])).

fof(f26,plain,
    ( sK0 != sK0
    | sK0 = k2_xboole_0(k1_tarski(sK0),sK0) ),
    inference(superposition,[],[f21,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,k1_tarski(X1)),k1_tarski(X1)) = X0
      | k2_xboole_0(k1_tarski(X1),X0) = X0 ) ),
    inference(resolution,[],[f19,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).

fof(f21,plain,(
    sK0 != k4_xboole_0(k2_xboole_0(sK0,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(definition_unfolding,[],[f14,f17,f16])).

fof(f17,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f14,plain,(
    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).

fof(f12,plain,
    ( ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0
   => sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (7038)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (7053)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.46  % (7049)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (7049)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f28,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) != X0) )),
% 0.21/0.46    inference(definition_unfolding,[],[f15,f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ( ! [X0] : (k1_ordinal1(X0) != X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : k1_ordinal1(X0) != X0),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    sK0 = k2_xboole_0(sK0,k1_tarski(sK0))),
% 0.21/0.46    inference(superposition,[],[f27,f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    sK0 = k2_xboole_0(k1_tarski(sK0),sK0)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    sK0 != sK0 | sK0 = k2_xboole_0(k1_tarski(sK0),sK0)),
% 0.21/0.46    inference(superposition,[],[f21,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,k1_tarski(X1)),k1_tarski(X1)) = X0 | k2_xboole_0(k1_tarski(X1),X0) = X0) )),
% 0.21/0.46    inference(resolution,[],[f19,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(X0,X1) | k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 | r2_hidden(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (~r2_hidden(X0,X1) => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    sK0 != k4_xboole_0(k2_xboole_0(sK0,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.46    inference(definition_unfolding,[],[f14,f17,f16])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0 => sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,negated_conjecture,(
% 0.21/0.46    ~! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0),
% 0.21/0.46    inference(negated_conjecture,[],[f7])).
% 0.21/0.46  fof(f7,conjecture,(
% 0.21/0.46    ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (7049)------------------------------
% 0.21/0.46  % (7049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (7049)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (7049)Memory used [KB]: 1535
% 0.21/0.46  % (7049)Time elapsed: 0.057 s
% 0.21/0.46  % (7049)------------------------------
% 0.21/0.46  % (7049)------------------------------
% 0.21/0.46  % (7051)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (7036)Success in time 0.108 s
%------------------------------------------------------------------------------
